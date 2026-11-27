import PEqualNP.Defs

-- The live-set and restriction lemmas follow L-meta-10554, L-meta-10802, L-meta-1674, L-meta-670 and L-meta-1667.
-- The rectangle argument follows L-meta-8459.
namespace PEqualNP.Outside.L_meta_15070
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 256
def zero : Sig := 0
def one : Sig := BitVec.allOnes 256
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

def bit (i : Fin 256) (a : Sig) : Bool := a.getLsbD i.val
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


abbrev Row := Fin 256
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
def W (a : Nat) : Sig := BitVec.ofNat 256 a
def full : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def xN : Nat → Nat
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
  | 6 => 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
  | _ => 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000
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
set_option maxRecDepth 8192 in
theorem W_inj {a b : Nat} (ha : a < 2^256) (hb : b < 2^256) (h : W a = W b) : a = b := by
  have := congrArg BitVec.toNat h
  simpa only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using this

def rootsW (R : List Nat) : List Sig := R.map fun i => W (xN i)
def LowN (u : Bool) (R : List Nat) (T L : Nat) : Prop := Lower u (rootsW R) (W T) L
abbrev SliceD := Nat × Nat × List Nat
def SliceN (u : Bool) (R : List Nat) (T : Nat) (s : SliceD) : Prop :=
  Slice u (rootsW R) (W T) (W s.1) s.2.1 ∧ ∀ v ∈ s.2.2, v ∈ R

def baseOK (T : Nat) (R : List Nat) (E : List (Nat × Nat × Nat)) : Bool :=
  decide (T < 2^256) && !(T.testBit 0) && (E.map Prod.fst == R) && !R.isEmpty && decide (rootsW R).Nodup &&
  R.all (fun i => !((xN i).testBit 0)) &&
  E.all (fun e => decide (e.2.1 < 256) && decide (e.2.2 < 256) && (T.testBit e.2.1 != T.testBit e.2.2) &&
    R.all (fun i => i == e.1 || (xN i).testBit e.2.1 == (xN i).testBit e.2.2))

abbrev BaseP (T : Nat) (R : List Nat) : Prop :=
  T < 2^256 ∧ plainWord (W T) = true ∧ (rootsW R).Nodup ∧ (rootsW R).all plainWord = true ∧
  (∀ a ∈ rootsW R, Essential (W T) (rootsW R) a) ∧ proper (W T)
theorem BaseP.lt {T R} (h : BaseP T R) : T < 2^256 := h.1
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
  (List.range 256).all (fun r => let q := rowOf vs w r
    Nat.blt q 256 && d.testBit q && (T.testBit q == G.testBit r)) &&
  R.all (fun i => (List.range 256).all (fun r => !((xN i).testBit (rowOf vs w r))) ||
    (List.range 256).all (fun r => (xN i).testBit (rowOf vs w r)) ||
    R'.any (fun j => (List.range 256).all (fun r => (xN i).testBit (rowOf vs w r) == (xN j).testBit r)))

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
def sepOK (T : Nat) (p : Nat × Nat) : Bool := Nat.blt p.1 256 && Nat.blt p.2 256 && T.testBit p.1 && !(T.testBit p.2)

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
  Nat.blt p 256 && Nat.blt n 256 && l.all (fun x => !(Nat.testBit x p) || Nat.testBit x n || Nat.beq x a)
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
    ∃ (hp : p < 256) (hn : n < 256), H.owns (W a) ⟨p,hp⟩ ⟨n,hn⟩ := by
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
set_option maxRecDepth 8192 in
theorem kw_sound {T k : Nat} {l : List Nat} (nd : (l.map W).Nodup) (size : l.length = k+1) (lt : ∀ x ∈ l, x < 2^256) (q : KwD)
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
    have fw : ∀ p n, findW l p n < 2^256 := by
      intro p n
      unfold findW
      cases hf : l.find? (fun x => Nat.testBit x p && !(Nat.testBit x n)) with
      | none => exact Nat.two_pow_pos 256
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
  | 0 => 0x2222222222222222222222222222222222222222222222222222222222222222
  | 1 => 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
  | 2 => 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0
  | 3 => 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00
  | 4 => 0xffff000000000000ffff000000000000ffff000000000000ffff0000
  | 5 => 0xffffffff000000000000000000000000ffffffff00000000
  | _ => 0xffffffffffffffff0000000000000000
def loM : Nat → Nat
  | 0 => 0x4444444444444444444444444444444444444444444444444444444444444444
  | 1 => 0x3030303030303030303030303030303030303030303030303030303030303030
  | 2 => 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00
  | 3 => 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000
  | 4 => 0xffff000000000000ffff000000000000ffff000000000000ffff00000000
  | 5 => 0xffffffff000000000000000000000000ffffffff0000000000000000
  | _ => 0xffffffffffffffff00000000000000000000000000000000
def keM : Nat → Nat
  | 0 => 0x9999999999999999999999999999999999999999999999999999999999999999
  | 1 => 0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3
  | 2 => 0xf00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f
  | 3 => 0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff
  | 4 => 0xffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff
  | 5 => 0xffffffff0000000000000000ffffffffffffffff0000000000000000ffffffff
  | _ => 0xffffffffffffffff00000000000000000000000000000000ffffffffffffffff
def shM : Nat → Nat
  | 0 => 1
  | 1 => 2
  | 2 => 4
  | 3 => 8
  | 4 => 16
  | 5 => 32
  | _ => 64
def swapN (i v : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.land v (keM i)) (Nat.shiftLeft (Nat.land v (hiM i)) (shM i))) (Nat.shiftRight (Nat.land v (loM i)) (shM i))
def sig (i : Nat) (r : Row) : Row :=
  if (hiM i).testBit r.val then Fin.ofNat 256 (r.val + shM i) else
    if (loM i).testBit r.val then Fin.ofNat 256 (r.val - shM i) else r
def swapFacts (i : Nat) (r : Row) : Prop :=
  ((keM i).testBit r.val = true ∧ (sig i r).val = r.val ∧ (decide (shM i ≤ r.val) && (hiM i).testBit (r.val - shM i)) = false ∧ (loM i).testBit (shM i + r.val) = false) ∨
  ((keM i).testBit r.val = false ∧ shM i ≤ r.val ∧ (sig i r).val = r.val - shM i ∧ (hiM i).testBit (r.val - shM i) = true ∧ (loM i).testBit (shM i + r.val) = false) ∨
  ((keM i).testBit r.val = false ∧ (sig i r).val = shM i + r.val ∧ (decide (shM i ≤ r.val) && (hiM i).testBit (r.val - shM i)) = false ∧ (loM i).testBit (shM i + r.val) = true)
theorem swap_facts : ∀ (i : Fin 7) (r : Row), swapFacts i.val r ∧ sig i.val (sig i.val r) = r := by
  unfold swapFacts
  decide +kernel
theorem swap_ok (i : Nat) (hi : i < 7) (v : Nat) : W (swapN i v) = rename (sig i) (W v) := by
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
def symOK (T : Nat) (l : List Nat) : Bool := l.all fun i => Nat.blt i 7 && Nat.beq (swapN i T) T
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
  | [x] => Nat.blt x (2^256)
  | x::y::l => Nat.blt x y && asc (y::l)
set_option maxRecDepth 8192 in
theorem asc_ok {l : List Nat} (h : asc l = true) : l.Pairwise (· < ·) ∧ ∀ x ∈ l, x < 2^256 := by
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

set_option maxRecDepth 8192 in
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
      have sub : ∀ x ∈ kidN p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb, x < 2^256 := by
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
        · have l1 : p.1 < 2^256 := lt _ ((pm _).mpr (Or.inl rfl))
          have l2 : p.2.1 < 2^256 := lt _ ((pm _).mpr (Or.inr (Or.inl rfl)))
          have la : Nat.land p.1 p.2.1 < 2^256 := Nat.lt_of_le_of_lt (Nat.and_le_left) l1
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


def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.or, [0, 2]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.or, [2, 10]⟩,
    ⟨.or, [3, 11]⟩,
    ⟨.or, [3, 8]⟩,
    ⟨.or, [4, 13]⟩,
    ⟨.and, [8, 4]⟩,
    ⟨.and, [9, 5]⟩,
    ⟨.and, [14, 6]⟩,
    ⟨.and, [12, 7]⟩,
    ⟨.or, [15, 16]⟩,
    ⟨.or, [19, 17]⟩,
    ⟨.or, [20, 18]⟩], 21⟩
theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel
theorem witnessSize : smallCircuit.gates.length = 14 := rfl
def pw0 : Nat := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def pw1 : Nat := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
def pw2 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def pw3 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
def pw4 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def pw5 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def pw6 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def pw7 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def pw8 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
def pw9 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def pw10 : Nat := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc
def pw11 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
def pw12 : Nat := 0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc
def pw13 : Nat := 0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc
def pw14 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0
def pw15 : Nat := 0xfc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc
def pw16 : Nat := 0xf0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c
def pw17 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def pw18 : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
def pw19 : Nat := 0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa
def pw20 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa
def pw21 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa
def pw22 : Nat := 0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc
def pw23 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0
def pw24 : Nat := 0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00
def pw25 : Nat := 0xeeee0000eeee0000eeee0000eeee0000eeee0000eeee0000eeee0000eeee
def pw26 : Nat := 0xfa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa
def pw27 : Nat := 0x3333303033333030333330303333303033333030333330303333303033333030
def pw28 : Nat := 0x5555550055555500555555005555550055555500555555005555550055555500
def pw29 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def pw30 : Nat := 0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc
def pw31 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def pw32 : Nat := 0x5555555500000000555555550000000055555555000000005555555500000000
def pw33 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def pw34 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def pw35 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def pw36 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def pw37 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def pw38 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def pw39 : Nat := 0x3030303000000000303030300000000030303030000000003030303
def pw40 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def pw41 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def pw42 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def pw43 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def pw44 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
def pw45 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
def pw46 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa
def pw47 : Nat := 0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc
def pw48 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0
def pw49 : Nat := 0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00
def pw50 : Nat := 0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000
def pw51 : Nat := 0xeeeeeeee00000000eeeeeeee00000000eeeeeeee00000000eeeeeeee
def pw52 : Nat := 0xfffafffafffafffafffafffafffafffafffafffafffafffafffafffafffafffa
def pw53 : Nat := 0xfffffafafffffafafffffafafffffafafffffafafffffafafffffafafffffafa
def pw54 : Nat := 0xfafa0000fafa0000fafa0000fafa0000fafa0000fafa0000fafa0000fafa
def pw55 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffee
def pw56 : Nat := 0xf0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a
def pw57 : Nat := 0xffffffaaffffffaaffffffaaffffffaaffffffaaffffffaaffffffaaffffffaa
def pw58 : Nat := 0xffaa0000ffaa0000ffaa0000ffaa0000ffaa0000ffaa0000ffaa0000ffaa
def pw59 : Nat := 0xffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeffffeeeeffffeeee
def pw60 : Nat := 0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a
def pw61 : Nat := 0xff00aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa
def pw62 : Nat := 0x5544554455445544554455445544554455445544554455445544554455445544
def pw63 : Nat := 0xffcc0000ffcc0000ffcc0000ffcc0000ffcc0000ffcc0000ffcc0000ffcc
def pw64 : Nat := 0x5555444455554444555544445555444455554444555544445555444455554444
def pw65 : Nat := 0xff00cc00ff00cc00ff00cc00ff00cc00ff00cc00ff00cc00ff00cc00ff00cc
def pw66 : Nat := 0x5550555055505550555055505550555055505550555055505550555055505550
def pw67 : Nat := 0xfffffff0fffffff0fffffff0fffffff0fffffff0fffffff0fffffff0fffffff0
def pw68 : Nat := 0xfff00000fff00000fff00000fff00000fff00000fff00000fff00000fff0
def pw69 : Nat := 0xfffffffffff0fff0fffffffffff0fff0fffffffffff0fff0fffffffffff0fff0
def pw70 : Nat := 0x5555505055555050555550505555505055555050555550505555505055555050
def pw71 : Nat := 0xff00f000ff00f000ff00f000ff00f000ff00f000ff00f000ff00f000ff00f0
def pw72 : Nat := 0xfffffffffffff0f0fffffffffffff0f0fffffffffffff0f0fffffffffffff0f0
def pw73 : Nat := 0x3333333330303030333333333030303033333333303030303333333330303030
def pw74 : Nat := 0xffffffccffffffccffffffccffffffccffffffccffffffccffffffccffffffcc
def pw75 : Nat := 0xf0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f000f0f0f00
def pw76 : Nat := 0xffffffffffffff00ffffffffffffff00ffffffffffffff00ffffffffffffff00
def pw77 : Nat := 0xf0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f000f0f0f0f0f000f00
def pw78 : Nat := 0xffff0000ff000000ffff0000ff000000ffff0000ff000000ffff0000ff00
def pw79 : Nat := 0xf0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f00000f0f0f0f0f0f0000
def pw80 : Nat := 0xff00ff00ff000000ff00ff00ff000000ff00ff00ff000000ff00ff00ff0000
def pw81 : Nat := 0xfffa0000fffa0000fffa0000fffa0000fffa0000fffa0000fffa0000fffa
def pw82 : Nat := 0xfffa0000fffa0000fffa0000fffa0000fffa0000fffa0000fffa0000fffa0000
def pw83 : Nat := 0xfffffffafffffffafffffffafffffffafffffffafffffffafffffffafffffffa
def pw84 : Nat := 0xffff00faffff00faffff00faffff00faffff00faffff00faffff00faffff00fa
def pw85 : Nat := 0xfa000000fa000000fa000000fa000000fa000000fa000000fa000000fa
def pw86 : Nat := 0xff00fa00ff00fa00ff00fa00ff00fa00ff00fa00ff00fa00ff00fa00ff00fa
def pw87 : Nat := 0xff00fa00ff00fa00ff00fa00ff00fa00ff00fa00ff00fa00ff00fa00ff00fa00
def pw88 : Nat := 0xff00fffaff00fffaff00fffaff00fffaff00fffaff00fffaff00fffaff00fffa
def pw89 : Nat := 0xffff0f0affff0f0affff0f0affff0f0affff0f0affff0f0affff0f0affff0f0a
def pw90 : Nat := 0xf0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a
def pw91 : Nat := 0xf0f0fffaf0f0fffaf0f0fffaf0f0fffaf0f0fffaf0f0fffaf0f0fffaf0f0fffa
def pw92 : Nat := 0xff0fff0aff0fff0aff0fff0aff0fff0aff0fff0aff0fff0aff0fff0aff0fff0a
def pw93 : Nat := 0xf0fff0faf0fff0faf0fff0faf0fff0faf0fff0faf0fff0faf0fff0faf0fff0fa
def pw94 : Nat := 0xffff5544ffff5544ffff5544ffff5544ffff5544ffff5544ffff5544ffff5544
def pw95 : Nat := 0xaaaaffeeaaaaffeeaaaaffeeaaaaffeeaaaaffeeaaaaffeeaaaaffeeaaaaffee
def pw96 : Nat := 0xff55ff44ff55ff44ff55ff44ff55ff44ff55ff44ff55ff44ff55ff44ff55ff44
def pw97 : Nat := 0xaaffaaeeaaffaaeeaaffaaeeaaffaaeeaaffaaeeaaffaaeeaaffaaeeaaffaaee
def pw98 : Nat := 0xffff5550ffff5550ffff5550ffff5550ffff5550ffff5550ffff5550ffff5550
def pw99 : Nat := 0x5555555055555550555555505555555055555550555555505555555055555550
def pw100 : Nat := 0xaaaafffaaaaafffaaaaafffaaaaafffaaaaafffaaaaafffaaaaafffaaaaafffa
def pw101 : Nat := 0xff55ff50ff55ff50ff55ff50ff55ff50ff55ff50ff55ff50ff55ff50ff55ff50
def pw102 : Nat := 0xaaffaafaaaffaafaaaffaafaaaffaafaaaffaafaaaffaafaaaffaafaaaffaafa
def pw103 : Nat := 0xf5f5f5f0f5f5f5f0f5f5f5f0f5f5f5f0f5f5f5f0f5f5f5f0f5f5f5f0f5f5f5f0
def pw104 : Nat := 0xf0f0f0c0f0f0f0c0f0f0f0c0f0f0f0c0f0f0f0c0f0f0f0c0f0f0f0c0f0f0f0c
def pw105 : Nat := 0xafafafaaafafafaaafafafaaafafafaaafafafaaafafafaaafafafaaafafafaa
def pw106 : Nat := 0x5555555555555500555555555555550055555555555555005555555555555500
def pw107 : Nat := 0xffff0f0fffff0f00ffff0f0fffff0f00ffff0f0fffff0f00ffff0f0fffff0f00
def pw108 : Nat := 0xf0f0fffff0f0fff0f0f0fffff0f0fff0f0f0fffff0f0fff0f0f0fffff0f0fff0
def pw109 : Nat := 0xff0fff0fff0fff00ff0fff0fff0fff00ff0fff0fff0fff00ff0fff0fff0fff00
def pw110 : Nat := 0xf0fff0fff0fff0f0f0fff0fff0fff0f0f0fff0fff0fff0f0f0fff0fff0fff0f0
def pw111 : Nat := 0x8888888888888888888888888888888888888888888888888888888888888888
def pw112 : Nat := 0x2222222222222222222222222222222222222222222222222222222222222222
def pw113 : Nat := 0x4444444444444444444444444444444444444444444444444444444444444444
def pw114 : Nat := 0xff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88
def pw115 : Nat := 0xffff8888ffff8888ffff8888ffff8888ffff8888ffff8888ffff8888ffff8888
def pw116 : Nat := 0xffffffff88888888ffffffff88888888ffffffff88888888ffffffff88888888
def pw117 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00
def pw118 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000
def pw119 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00
def pw120 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def pw121 : Nat := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0
def pw122 : Nat := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a
def pw123 : Nat := 0x5050505050505050505050505050505050505050505050505050505050505050
def pw124 : Nat := 0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa
def pw125 : Nat := 0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa
def pw126 : Nat := 0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa
def pw127 : Nat := 0x3030303030303030303030303030303030303030303030303030303030303030
def pw128 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0
def pw129 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0
def pw130 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0
def pw131 : Nat := 0xf2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2
def pw132 : Nat := 0xecececececececececececececececececececececececececececececececec
def pw133 : Nat := 0xffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0
def pw134 : Nat := 0xffffa0a0ffffa0a0ffffa0a0ffffa0a0ffffa0a0ffffa0a0ffffa0a0ffffa0a0
def pw135 : Nat := 0xffffffffa0a0a0a0ffffffffa0a0a0a0ffffffffa0a0a0a0ffffffffa0a0a0a0
def pw136 : Nat := 0xffff00aaffff00aaffff00aaffff00aaffff00aaffff00aaffff00aaffff00aa
def pw137 : Nat := 0xff00ffaaff00ffaaff00ffaaff00ffaaff00ffaaff00ffaaff00ffaaff00ffaa
def pw138 : Nat := 0x3333333322222222333333332222222233333333222222223333333322222222
def pw139 : Nat := 0xf0f0f0f0fafafafaf0f0f0f0fafafafaf0f0f0f0fafafafaf0f0f0f0fafafafa
def pw140 : Nat := 0xffffffff30303030ffffffff30303030ffffffff30303030ffffffff30303030
def pw141 : Nat := 0xaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafa
def pw142 : Nat := 0xaaaafafaaaaafafaaaaafafaaaaafafaaaaafafaaaaafafaaaaafafaaaaafafa
def pw143 : Nat := 0xccccccccfcfcfcfcccccccccfcfcfcfcccccccccfcfcfcfcccccccccfcfcfcfc
def pw144 : Nat := 0x22f222f222f222f222f222f222f222f222f222f222f222f222f222f222f222f2
def pw145 : Nat := 0x2222f2f22222f2f22222f2f22222f2f22222f2f22222f2f22222f2f22222f2f2
def pw146 : Nat := 0xf000f0aafaaafa00f000f0aafaaafa00f000f0aafaaafa00f000f0aafaaafa
def pw147 : Nat := 0xf0f0aaaafafa0000f0f0aaaafafa0000f0f0aaaafafa0000f0f0aaaafafa
def pw148 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def pw149 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def pw150 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def pw151 : Nat := 0x101010101010101010101010101010101010101010101010101010101010101
def pw152 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000
def pw153 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def pw154 : Nat := 0x333333333333333300000000000000003333333333333333
def pw155 : Nat := 0x30303030000000003030303000000000303030300000000030303030
def pw156 : Nat := 0xc0c0c0c0c0c0c0c00000000000000000c0c0c0c0c0c0c0c
def pw157 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
def pw158 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0
def pw159 : Nat := 0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc
def pw160 : Nat := 0xeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaea
def pw161 : Nat := 0xffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0
def pw162 : Nat := 0xffffc0c0ffffc0c0ffffc0c0ffffc0c0ffffc0c0ffffc0c0ffffc0c0ffffc0c0
def pw163 : Nat := 0xffffffffc0c0c0c0ffffffffc0c0c0c0ffffffffc0c0c0c0ffffffffc0c0c0c0
def pw164 : Nat := 0xffffffffffffffffc0c0c0c0c0c0c0c0ffffffffffffffffc0c0c0c0c0c0c0c0
def pw165 : Nat := 0x5454545454545454545454545454545454545454545454545454545454545454
def pw166 : Nat := 0xfffcfffcfffcfffcfffcfffcfffcfffcfffcfffcfffcfffcfffcfffcfffcfffc
def pw167 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcfffffcfcfffffcfcfffffcfcfffffcfc
def pw168 : Nat := 0xfcfc0000fcfc0000fcfc0000fcfc0000fcfc0000fcfc0000fcfc0000fcfc
def pw169 : Nat := 0xff0cff0cff0cff0cff0cff0cff0cff0cff0cff0cff0cff0cff0cff0cff0cff0c
def pw170 : Nat := 0xffff0c0cffff0c0cffff0c0cffff0c0cffff0c0cffff0c0cffff0c0cffff0c0c
def pw171 : Nat := 0xff30ff30ff30ff30ff30ff30ff30ff30ff30ff30ff30ff30ff30ff30ff30ff30
def pw172 : Nat := 0xffff3030ffff3030ffff3030ffff3030ffff3030ffff3030ffff3030ffff3030
def pw173 : Nat := 0xf0fcf0fcf0fcf0fcf0fcf0fcf0fcf0fcf0fcf0fcf0fcf0fcf0fcf0fcf0fcf0fc
def pw174 : Nat := 0xffff00ccffff00ccffff00ccffff00ccffff00ccffff00ccffff00ccffff00cc
def pw175 : Nat := 0xf0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c0f0f0c0c
def pw176 : Nat := 0xf0f0fcfcf0f0fcfcf0f0fcfcf0f0fcfcf0f0fcfcf0f0fcfcf0f0fcfcf0f0fcfc
def pw177 : Nat := 0xff00ffccff00ffccff00ffccff00ffccff00ffccff00ffccff00ffccff00ffcc
def pw178 : Nat := 0x3330333033303330333033303330333033303330333033303330333033303330
def pw179 : Nat := 0xccfcccfcccfcccfcccfcccfcccfcccfcccfcccfcccfcccfcccfcccfcccfcccfc
def pw180 : Nat := 0xffff00f0ffff00f0ffff00f0ffff00f0ffff00f0ffff00f0ffff00f0ffff00f0
def pw181 : Nat := 0xccccfcfcccccfcfcccccfcfcccccfcfcccccfcfcccccfcfcccccfcfcccccfcfc
def pw182 : Nat := 0xff00fff0ff00fff0ff00fff0ff00fff0ff00fff0ff00fff0ff00fff0ff00fff0
def pw183 : Nat := 0x3333330033333300333333003333330033333300333333003333330033333300
def pw184 : Nat := 0x5554555455545554555455545554555455545554555455545554555455545554
def pw185 : Nat := 0x5555545455555454555554545555545455555454555554545555545455555454
def pw186 : Nat := 0xffccf0c0ffccf0c0ffccf0c0ffccf0c0ffccf0c0ffccf0c0ffccf0c0ffccf0c0
def pw187 : Nat := 0xffffffccffffffcc0000000000000000ffffffccffffffcc
def pw188 : Nat := 0xfff0ccc0fff0ccc0fff0ccc0fff0ccc0fff0ccc0fff0ccc0fff0ccc0fff0ccc0
def pw189 : Nat := 0xfffffff000000000fffffff000000000fffffff000000000fffffff0
def pw190 : Nat := 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000
def p1_T : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def p1_R : List Nat := [0, 1, 2]
def p1_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5)]
theorem p1_B : baseOK p1_T p1_R p1_E = true := by decide +kernel
def p1_Z : List SliceD := []
theorem p1_Y : ∀ s ∈ p1_Z, SliceN true p1_R p1_T s := by
  intro s h
  cases h
def p1_C : List (Nat × List Nat) := []
def p1_t : Tabs := (p1_C.map (mkCut true p1_Z),[(5,4),(6,4),(3,2),(3,1),(6,2),(5,1)],[],[[]])
theorem p1_W : TabsP true p1_R p1_T p1_t := ⟨cutsGood p1_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p1_D3 : List StD := [
([pw0,pw1,pw2],[1,5,9,13,17,21],[15,53,58])]
def p1_D2 : List StD := []
theorem p1_I2 : LevelN true p1_T 2 p1_D2 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p1_C3x0 : levelOK true p1_T p1_t 2 (p1_D2.map Prod.fst) ((p1_D3.drop (0*32)).take 32) = true := by decide +kernel
theorem p1_I3 : LevelN true p1_T 3 p1_D3 := levelStep p1_B p1_W p1_I2 (chunks 32 p1_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p1_C3x0
  ))
theorem p1_L : LowN true p1_R p1_T 4 := lowSearch p1_B p1_I3 (by decide +kernel)
def p2_T : Nat := 0xeac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8
def p2_R : List Nat := [0, 1, 2, 3]
def p2_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,1,9)]
theorem p2_B : baseOK p2_T p2_R p2_E = true := by decide +kernel
def p2_Z : List SliceD := []
theorem p2_Y : ∀ s ∈ p2_Z, SliceN true p2_R p2_T s := by
  intro s h
  cases h
def p2_C : List (Nat × List Nat) := []
def p2_t : Tabs := (p2_C.map (mkCut true p2_Z),[(6,4),(3,1),(3,2),(9,12),(6,2),(9,1),(9,0),(6,12),(9,5)],[],[[]])
theorem p2_W : TabsP true p2_R p2_T p2_t := ⟨cutsGood p2_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p2_D3 : List StD := [
([pw0,pw1,pw2,pw3],[1,21,5,9,17,13,25,29,33],[5,56,74,5,131,274])]
def p2_D2 : List StD := []
theorem p2_I2 : LevelN true p2_T 2 p2_D2 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p2_C3x0 : levelOK true p2_T p2_t 2 (p2_D2.map Prod.fst) ((p2_D3.drop (0*32)).take 32) = true := by decide +kernel
theorem p2_I3 : LevelN true p2_T 3 p2_D3 := levelStep p2_B p2_W p2_I2 (chunks 32 p2_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p2_C3x0
  ))
theorem p2_L : LowN true p2_R p2_T 4 := lowSearch p2_B p2_I3 (by decide +kernel)
def p3_T : Nat := 0xfeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeea
def p3_R : List Nat := [0, 1, 2, 3]
def p3_E : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6),(3,2,10)]
theorem p3_B : baseOK p3_T p3_R p3_E = true := by decide +kernel
def p3_Z : List SliceD := [(pw4,4,[1, 2, 3])]
theorem p3_Y : ∀ s ∈ p3_Z, SliceN true p3_R p3_T s := by
  unfold p3_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p3_B p1_B p1_L (by decide +kernel),by simp⟩
def p3_C : List (Nat × List Nat) := [(0,[])]
def p3_t : Tabs := (p3_C.map (mkCut true p3_Z),[(1,0),(6,4),(3,2)],[],[[]])
theorem p3_W : TabsP true p3_R p3_T p3_t := ⟨cutsGood p3_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p3_D4 : List StD := [
([pw0,pw1,pw2,pw3],[0,1,5,9],[15,3,3,1,5,1])]
def p3_D3 : List StD := []
theorem p3_I3 : LevelN true p3_T 3 p3_D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p3_C4x0 : levelOK true p3_T p3_t 3 (p3_D3.map Prod.fst) ((p3_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p3_I4 : LevelN true p3_T 4 p3_D4 := levelStep p3_B p3_W p3_I3 (chunks 32 p3_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p3_C4x0
  ))
theorem p3_L : LowN true p3_R p3_T 5 := lowSearch p3_B p3_I4 (by decide +kernel)
def p4_T : Nat := 0xeae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8
def p4_R : List Nat := [0, 1, 2, 3]
def p4_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem p4_B : baseOK p4_T p4_R p4_E = true := by decide +kernel
def p4_Z : List SliceD := [(pw5,4,[0, 1, 2])]
theorem p4_Y : ∀ s ∈ p4_Z, SliceN true p4_R p4_T s := by
  unfold p4_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p4_B p1_B p1_L (by decide +kernel),by simp⟩
def p4_C : List (Nat × List Nat) := [(0,[])]
def p4_t : Tabs := (p4_C.map (mkCut true p4_Z),[(5,4),(6,4),(3,2),(3,1),(6,2),(5,1)],[],[[]])
theorem p4_W : TabsP true p4_R p4_T p4_t := ⟨cutsGood p4_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p4_D4 : List StD := [
([pw0,pw1,pw2,pw3],[0,1,5,17,9,13,21],[54,90,3,108,5,9])]
def p4_D3 : List StD := []
theorem p4_I3 : LevelN true p4_T 3 p4_D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p4_C4x0 : levelOK true p4_T p4_t 3 (p4_D3.map Prod.fst) ((p4_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p4_I4 : LevelN true p4_T 4 p4_D4 := levelStep p4_B p4_W p4_I3 (chunks 32 p4_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p4_C4x0
  ))
theorem p4_L : LowN true p4_R p4_T 5 := lowSearch p4_B p4_I4 (by decide +kernel)
def p5_T : Nat := 0xfeeafcc8feeafcc8feeafcc8feeafcc8feeafcc8feeafcc8feeafcc8feeafcc8
def p5_R : List Nat := [0, 1, 2, 3, 4]
def p5_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,2,10),(4,1,17)]
theorem p5_B : baseOK p5_T p5_R p5_E = true := by decide +kernel
def p5_Z : List SliceD := [(pw6,4,[1, 2, 3]),(pw7,4,[0, 1, 3, 4]),(pw5,4,[0, 1, 2, 4]),(pw8,5,[0, 1, 2, 3]),(pw9,5,[1, 2, 3, 0])]
theorem p5_Y : ∀ s ∈ p5_Z, SliceN true p5_R p5_T s := by
  unfold p5_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p5_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p5_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p5_B p2_B p2_L (by decide +kernel),mkSlice (w:=16) p5_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p5_B p4_B p4_L (by decide +kernel),by simp⟩
def p5_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[])]
def p5_t : Tabs := (p5_C.map (mkCut true p5_Z),[(3,2),(17,16),(21,20),(25,24),(12,8),(6,4),(6,2),(12,4),(10,8),(10,2),(7,4),(12,5),(3,5),(3,1),(6,20),(17,1),(6,18),(21,5),(17,9),(12,9),(6,0),(17,5),(11,8),(3,9),(10,24),(10,18),(25,9),(10,0),(12,20),(12,0),(12,1),(17,0),(10,16),(22,2),(7,0),(6,16),(12,16)],[],[[]])
theorem p5_W : TabsP true p5_R p5_T p5_t := ⟨cutsGood p5_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p5_D6 : List StD := [
([pw0,pw1,pw2,pw3,pw8],[0,1,12,3,4,8,5,17,25,29,9,13,21,33,37],[67,1027,2051,67,4504,25128,5,952,5,5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p5_D5 : List StD := [
([pw0,pw1,pw2,pw10,pw3,pw8],[1,37,21,61,9,25,29,8,5,17,41,45,49,53,57,65,69,73,3],[1029,17,257,2051,17,4132,8192,70,16396,512,66,32808,262274,65544,131082]),
([pw11,pw0,pw1,pw2,pw3,pw8],[5,29,61,1,17,37,21,12,16,25,45,53,57,73,77,81,85],[9,2048,512,34,388,9,16401,1027,9,32848,34,4164,34,65556,8198]),
([pw0,pw1,pw2,pw3,pw12,pw8],[1,25,33,61,13,17,37,4,5,29,53,77,85,89,93,97,101,105,3],[8197,2051,17,257,17,38,16452,1024,32780,34,262274,4106,512,65608,131080]),
([pw13,pw0,pw1,pw2,pw3,pw8],[5,17,61,1,25,29,33,12,16,37,45,53,73,77,85,97,109],[9,2048,18,512,388,9,8195,1057,9,18,65632,32836,18,16390,4132]),
([pw0,pw1,pw2,pw3,pw14,pw8],[21,1,61,29,53,4,9,17,69,25,33,45,57,77,113],[17,8322,2058,66,66,17,1025,17,4101,40,512,388,32,16396,260])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p5_D4 : List StD := [
([pw15,pw0,pw1,pw2,pw8],[1,25,37,69,109,61,117,41,45,53,121,125,129],[261,532,70,44,145,1027,2057,82,4120,42]),
([pw16,pw0,pw1,pw3,pw8],[1,25,37,61,81,117,53,77,121,125,133,137,141,145],[131,82,38,1034,2065,261,521,52,4120,8204])]
def p5_D3 : List StD := []
theorem p5_I3 : LevelN true p5_T 3 p5_D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5_C4x0 : levelOK true p5_T p5_t 3 (p5_D3.map Prod.fst) ((p5_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p5_I4 : LevelN true p5_T 4 p5_D4 := levelStep p5_B p5_W p5_I3 (chunks 32 p5_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_C4x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5_C5x0 : levelOK true p5_T p5_t 4 (p5_D4.map Prod.fst) ((p5_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p5_I5 : LevelN true p5_T 5 p5_D5 := levelStep p5_B p5_W p5_I4 (chunks 32 p5_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_C5x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5_C6x0 : levelOK true p5_T p5_t 5 (p5_D5.map Prod.fst) ((p5_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p5_I6 : LevelN true p5_T 6 p5_D6 := levelStep p5_B p5_W p5_I5 (chunks 32 p5_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_C6x0
  ))
theorem p5_L : LowN true p5_R p5_T 7 := lowSearch p5_B p5_I6 (by decide +kernel)
def p6_T : Nat := 0xfeeafce8feeafce8feeafce8feeafce8feeafce8feeafce8feeafce8feeafce8
def p6_R : List Nat := [0, 1, 2, 3, 4]
def p6_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,2,10),(4,1,17)]
theorem p6_B : baseOK p6_T p6_R p6_E = true := by decide +kernel
def p6_Z : List SliceD := [(pw17,4,[0, 2, 3, 4]),(pw6,4,[1, 2, 3]),(pw7,4,[0, 1, 3, 4]),(pw5,5,[0, 1, 2, 4]),(pw8,5,[0, 1, 2, 3])]
theorem p6_Y : ∀ s ∈ p6_Z, SliceN true p6_R p6_T s := by
  unfold p6_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p6_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p6_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p6_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p6_B p4_B p4_L (by decide +kernel),mkSlice (w:=16) p6_B p3_B p3_L (by decide +kernel),by simp⟩
def p6_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[])]
def p6_t : Tabs := (p6_C.map (mkCut true p6_Z),[(6,4),(3,2),(3,0),(5,4),(25,24),(3,1),(6,2),(10,2),(10,0),(12,4),(17,16),(17,24),(6,20),(6,18),(17,1),(17,9),(5,1),(26,2),(10,16),(12,16)],[],[[]])
theorem p6_W : TabsP true p6_R p6_T p6_t := ⟨cutsGood p6_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p6_D6 : List StD := [
([pw0,pw1,pw2,pw3,pw8],[4,0,1,5,12,16,8,17,25,29,9,13,21,33,37,3],[1039,2057,137,137,37190,8726,39,17232,33,49])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p6_D5 : List StD := [
([pw0,pw1,pw2,pw10,pw3,pw8],[13,29,0,57,5,25,41,4,12,16,1,21,37,45,49,53,61,3],[17,17,65,8195,65,36,2048,6,17412,4,4098,32808,131330,648,65546])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p6_D4 : List StD := [
([pw15,pw0,pw1,pw2,pw8],[5,29,25,33,41,57,1,13,21,65,69,73,77],[19,266,518,1058,17,129,17,76,2088,4132])]
def p6_D3 : List StD := []
theorem p6_I3 : LevelN true p6_T 3 p6_D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p6_C4x0 : levelOK true p6_T p6_t 3 (p6_D3.map Prod.fst) ((p6_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p6_I4 : LevelN true p6_T 4 p6_D4 := levelStep p6_B p6_W p6_I3 (chunks 32 p6_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p6_C4x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p6_C5x0 : levelOK true p6_T p6_t 4 (p6_D4.map Prod.fst) ((p6_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p6_I5 : LevelN true p6_T 5 p6_D5 := levelStep p6_B p6_W p6_I4 (chunks 32 p6_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p6_C5x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p6_C6x0 : levelOK true p6_T p6_t 5 (p6_D5.map Prod.fst) ((p6_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p6_I6 : LevelN true p6_T 6 p6_D6 := levelStep p6_B p6_W p6_I5 (chunks 32 p6_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p6_C6x0
  ))
theorem p6_L : LowN true p6_R p6_T 7 := lowSearch p6_B p6_I6 (by decide +kernel)
def p7_T : Nat := 0xfeeefac0feeefac0feeefac0feeefac0feeefac0feeefac0feeefac0feeefac0
def p7_R : List Nat := [0, 1, 2, 3, 4]
def p7_E : List (Nat × Nat × Nat) := [(0,8,9),(1,4,6),(2,2,6),(3,1,9),(4,1,17)]
theorem p7_B : baseOK p7_T p7_R p7_E = true := by decide +kernel
def p7_Z : List SliceD := [(pw4,4,[1, 2, 3, 4]),(pw17,4,[0, 3, 2, 4]),(pw7,4,[0, 4, 1, 3]),(pw5,4,[1, 4, 0, 2]),(pw9,4,[2, 3, 0, 1])]
theorem p7_Y : ∀ s ∈ p7_Z, SliceN true p7_R p7_T s := by
  unfold p7_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p7_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p7_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p7_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p7_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p7_B p2_B p2_L (by decide +kernel),by simp⟩
def p7_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[])]
def p7_t : Tabs := (p7_C.map (mkCut true p7_Z),[(9,8),(11,10),(7,5),(21,20),(7,3),(9,1),(17,1),(12,8),(26,24),(11,3),(18,2),(12,4),(28,24),(21,5),(28,20),(26,10),(6,5),(6,3),(6,2),(6,4),(9,3),(17,5),(18,10),(7,4),(18,16),(12,5),(17,16),(18,3),(17,3),(7,2),(9,0),(17,0),(12,10),(9,10),(11,8),(14,8),(9,5),(12,20),(17,20),(21,16),(18,24),(26,16),(12,24),(12,0),(7,1),(12,16),(6,0),(6,1),(7,0),(11,2),(18,0),(18,8),(9,2),(17,2),(17,4)],[],[[]])
theorem p7_W : TabsP true p7_R p7_T p7_t := ⟨cutsGood p7_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p7_D6 : List StD := [
([pw0,pw1,pw2,pw3,pw8],[3,0,4,8,12,16,1,9,17,13,21,29,33,5,25,37,41,45,49,53,57,61],[8391,843,1619,16995,2445,37013,69797,133401,786729,3146801])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p7_D5 : List StD := [
([pw0,pw1,pw18,pw2,pw3,pw8],[25,45,73,5,9,21,29,41,16,1,65,69,77,81,85,89,3],[1048,512,2060,42,137,4096,84,8210,145,68,34,65793,38,16389,32771]),
([pw0,pw1,pw2,pw19,pw3,pw8],[21,41,77,13,17,25,45,97,12,1,65,69,73,81,85,89,93,3],[66564,2072,512,73,42,132,132,8197,38,4096,81,16402,131329,34,32771]),
([pw0,pw1,pw2,pw3,pw20,pw8],[25,73,77,21,41,1,9,17,29,45,61,81,85,101,105],[68,130,8232,16384,49,262,2060,68,21,258,130,4099,512,1033,17]),
([pw0,pw1,pw2,pw3,pw8,pw21],[45,73,77,21,25,9,17,1,29,41,57,81,85,105,109,113],[36,66,9,24592,128,262,2053,32788,36,11,4114,66,1025,9,512]),
([pw0,pw1,pw2,pw10,pw3,pw8],[25,45,73,77,1,37,41,5,21,29,53,65,69,89,93,97,117,121,125,129],[18440,69636,144,131090,262161,524300,32768,42,73,512,38,1029,258,65,8195]),
([pw0,pw1,pw2,pw3,pw12,pw8],[1,73,25,105,29,33,37,41,8,21,69,77,81,85,89,133,137,3],[98305,1027,9,9,9,18,4192,2048,164,18,131330,8198,512,16452,132]),
([pw0,pw1,pw2,pw3,pw8,pw22],[1,45,73,29,5,37,41,25,49,69,77,89,97,105,113,121],[17,517,32771,8193,17,12,34,20544,1024,14,260,12,2114,34,128]),
([pw0,pw1,pw2,pw3,pw14,pw8],[77,1,13,29,53,25,33,45,21,65,73,93,97,105,141,145,149],[2561,6,6,8194,6,16393,65,4097,65,32904,1024,56,256,65680,48]),
([pw0,pw1,pw2,pw3,pw8,pw23],[45,77,1,21,53,97,105,4,25,49,65,73,81,85,93,121,149,153,157,3],[17410,393220,32773,68,68,34,4099,34,524418,9,8720,2048,65553,9,256]),
([pw0,pw1,pw2,pw3,pw8,pw24],[73,77,29,105,1,61,97,0,21,25,57,65,69,89,93,117,161,165,169,3],[18434,36865,24,24,524424,7,196610,66,66,5,262177,5,9248,256,512])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p7_D4 : List StD := [
([pw25,pw0,pw1,pw2,pw3],[73,125,5,9,25,29,21,45,69,77,81],[6,536,49,208,6,259,6,41,1096,33]),
([pw26,pw0,pw1,pw2,pw8],[21,25,77,121,41,173,45,65,69,81,177,181],[73,517,65,19,140,296,26,1060,22,2082]),
([pw16,pw0,pw1,pw3,pw8],[41,73,185,25,173,29,1,69,81,117,181,189,193,197],[642,38,34,11,6148,8272,9,276,13,1041]),
([pw27,pw0,pw2,pw3,pw8],[45,77,185,21,201,1,29,65,85,93,97,105,189,193,205],[642,70,11,1026,12292,9,2080,13,276,16401]),
([pw28,pw1,pw2,pw3,pw8],[1,29,77,73,121,125,45,89,105,137,209,213,217],[517,11,81,257,14,1044,2084,10,4130,176])]
def p7_D3 : List StD := []
theorem p7_I3 : LevelN true p7_T 3 p7_D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p7_C4x0 : levelOK true p7_T p7_t 3 (p7_D3.map Prod.fst) ((p7_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p7_I4 : LevelN true p7_T 4 p7_D4 := levelStep p7_B p7_W p7_I3 (chunks 32 p7_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p7_C4x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p7_C5x0 : levelOK true p7_T p7_t 4 (p7_D4.map Prod.fst) ((p7_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p7_I5 : LevelN true p7_T 5 p7_D5 := levelStep p7_B p7_W p7_I4 (chunks 32 p7_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p7_C5x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p7_C6x0 : levelOK true p7_T p7_t 5 (p7_D5.map Prod.fst) ((p7_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p7_I6 : LevelN true p7_T 6 p7_D6 := levelStep p7_B p7_W p7_I5 (chunks 32 p7_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p7_C6x0
  ))
theorem p7_L : LowN true p7_R p7_T 7 := lowSearch p7_B p7_I6 (by decide +kernel)
def p8_T : Nat := 0xeee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8
def p8_R : List Nat := [0, 1, 2, 3]
def p8_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem p8_B : baseOK p8_T p8_R p8_E = true := by decide +kernel
def p8_Z : List SliceD := [(pw7,4,[0, 1, 3])]
theorem p8_Y : ∀ s ∈ p8_Z, SliceN true p8_R p8_T s := by
  unfold p8_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p8_B p1_B p1_L (by decide +kernel),by simp⟩
def p8_C : List (Nat × List Nat) := [(0,[])]
def p8_t : Tabs := (p8_C.map (mkCut true p8_Z),[(5,4),(6,4),(3,2),(3,1),(6,2),(5,1),(10,2),(9,8),(9,1),(10,8)],[],[[]])
theorem p8_W : TabsP true p8_R p8_T p8_t := ⟨cutsGood p8_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p8_D4 : List StD := [
([pw0,pw1,pw2,pw3],[1,5,17,25,9,13,21,33,0,29,37],[51,85,649,102,1162,268])]
def p8_D3 : List StD := []
theorem p8_I3 : LevelN true p8_T 3 p8_D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p8_C4x0 : levelOK true p8_T p8_t 3 (p8_D3.map Prod.fst) ((p8_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p8_I4 : LevelN true p8_T 4 p8_D4 := levelStep p8_B p8_W p8_I3 (chunks 32 p8_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p8_C4x0
  ))
theorem p8_L : LowN true p8_R p8_T 5 := lowSearch p8_B p8_I4 (by decide +kernel)
def p9_T : Nat := 0xfffefeeefffafac0fffefeeefffafac0fffefeeefffafac0fffefeeefffafac0
def p9_R : List Nat := [0, 1, 2, 3, 4, 5]
def p9_E : List (Nat × Nat × Nat) := [(0,8,9),(1,4,6),(2,2,6),(3,1,9),(4,1,17),(5,1,33)]
theorem p9_B : baseOK p9_T p9_R p9_E = true := by decide +kernel
def p9_Z : List SliceD := [(pw4,7,[1, 2, 3, 4, 5]),(pw17,7,[0, 3, 4, 2, 5]),(pw7,7,[5, 0, 3, 4, 1]),(pw5,7,[0, 1, 2, 4, 5]),(pw9,7,[0, 1, 2, 3, 5]),(pw29,7,[2, 3, 4, 0, 1]),(pw11,5,[5, 3, 4, 0]),(pw30,5,[2, 0, 3, 4]),(pw31,4,[2, 3, 4]),(pw32,5,[1, 2, 3, 4]),(pw33,4,[1, 2, 4, 5]),(pw6,4,[1, 2, 3, 5]),(pw34,5,[2, 3, 4, 1]),(pw35,5,[0, 3, 4, 5]),(pw36,5,[3, 4, 0, 2]),(pw37,4,[0, 5, 1, 4]),(pw38,4,[0, 5, 1, 3]),(pw39,4,[0, 3, 4]),(pw40,4,[1, 5, 0, 2]),(pw41,4,[0, 3, 2, 5]),(pw42,4,[0, 4, 2, 5]),(pw43,4,[2, 3, 0, 1]),(pw44,4,[2, 4, 0, 1])]
theorem p9_Y : ∀ s ∈ p9_Z, SliceN true p9_R p9_T s := by
  unfold p9_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p9_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p9_B p6_B p6_L (by decide +kernel),mkSlice (w:=0) p9_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p9_B p7_B p7_L (by decide +kernel),mkSlice (w:=0) p9_B p7_B p7_L (by decide +kernel),mkSlice (w:=0) p9_B p6_B p6_L (by decide +kernel),mkSlice (w:=2) p9_B p3_B p3_L (by decide +kernel),mkSlice (w:=2) p9_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p9_B p1_B p1_L (by decide +kernel),mkSlice (w:=32) p9_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p9_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p9_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p9_B p4_B p4_L (by decide +kernel),mkSlice (w:=0) p9_B p4_B p4_L (by decide +kernel),mkSlice (w:=0) p9_B p8_B p8_L (by decide +kernel),mkSlice (w:=0) p9_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p9_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p9_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p9_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p9_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p9_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p9_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p9_B p2_B p2_L (by decide +kernel),by simp⟩
def p9_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(3,[129]),(4,[129]),(5,[385]),(1,[385]),(9,[]),(3,[257]),(4,[257]),(1,[129]),(2,[261]),(10,[]),(4,[385]),(5,[389]),(1,[257]),(2,[389]),(3,[385]),(11,[]),(5,[393]),(2,[129]),(1,[513]),(3,[513]),(4,[513]),(12,[]),(0,[129]),(13,[]),(3,[261]),(4,[261]),(0,[257]),(4,[389]),(0,[385]),(3,[389]),(0,[513]),(3,[517]),(4,[517]),(14,[]),(0,[261]),(1,[389]),(15,[]),(4,[393]),(5,[129]),(0,[389]),(1,[393]),(3,[393]),(16,[]),(5,[257]),(0,[517]),(3,[521]),(1,[525]),(4,[521]),(17,[]),(0,[393]),(1,[261]),(2,[393]),(18,[]),(5,[261]),(0,[521]),(2,[257]),(1,[517]),(4,[525]),(0,[525]),(1,[521]),(3,[525]),(2,[385]),(0,[514]),(2,[517,22]),(4,[129,534]),(3,[129,534]),(1,[385,129]),(7,[129]),(1,[385,257]),(5,[385,129]),(5,[385,257]),(0,[263]),(0,[262]),(0,[260]),(2,[262]),(4,[257,406]),(2,[391]),(0,[391]),(0,[388]),(0,[390]),(2,[390]),(3,[257,406]),(3,[131]),(0,[258]),(19,[]),(3,[259]),(0,[395]),(0,[394]),(2,[261,406]),(20,[]),(4,[131]),(0,[386]),(4,[259]),(4,[387]),(2,[389,278]),(3,[258]),(3,[395]),(2,[395]),(0,[261,406]),(3,[523]),(2,[258]),(21,[]),(4,[258]),(4,[395]),(2,[394]),(0,[389,278]),(22,[]),(4,[523]),(2,[386]),(0,[517,22]),(3,[521,150]),(4,[521,150]),(4,[386]),(3,[386]),(5,[261,406]),(4,[390]),(3,[390]),(4,[394]),(3,[394]),(1,[261,406]),(4,[527]),(3,[527]),(6,[129]),(6,[257]),(3,[390,21]),(3,[392,21]),(0,[392,149]),(0,[261,404]),(0,[389,276]),(0,[258,405]),(0,[386,277]),(3,[523,405]),(4,[523,405]),(3,[527,277]),(3,[389,278]),(3,[525,22]),(0,[393,392,153])]
def p9_t : Tabs := (p9_C.map (mkCut true p9_Z),[(9,8),(11,10),(7,5),(37,36),(7,3),(9,1),(17,16),(17,1),(33,1),(12,8),(42,40),(11,3),(50,48),(19,3),(34,2),(12,4),(20,16),(20,4),(44,40),(37,5),(24,16),(24,8),(44,36),(42,10),(52,36),(50,18),(6,3),(19,18),(6,2),(33,5),(6,5),(34,32),(6,4),(9,5),(17,5),(41,40),(13,5),(49,48),(21,5),(33,32),(6,0),(35,3),(33,0),(14,10),(22,18),(6,10),(26,18),(34,10),(6,18),(26,10),(34,18),(52,48),(56,48),(56,40),(37,4),(34,0),(42,8),(50,16),(24,40),(7,4),(9,3),(17,3),(12,36),(24,18),(20,36),(24,10),(12,5),(12,10),(11,8),(22,16),(20,0),(20,5),(19,16),(14,8),(34,3),(7,2),(33,3),(34,48),(50,32),(34,40),(42,32),(7,1),(33,36),(37,32),(9,10),(26,16),(26,8),(12,40),(9,2),(17,2),(33,40),(33,48),(9,16),(9,4),(17,4),(9,0),(12,0),(24,0),(24,32),(17,8),(50,2),(17,0),(25,1),(42,2),(11,2),(44,32),(17,18),(11,18),(41,48),(20,32),(12,16),(21,1),(6,8),(20,8),(12,32),(13,1),(19,2),(21,4),(14,18),(44,48),(13,4),(6,1),(7,0),(13,8),(33,4),(37,1),(11,16),(13,16),(14,16),(9,18)],[],[[]])
theorem p9_W : TabsP true p9_R p9_T p9_t := ⟨cutsGood p9_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p9_D9 : List StD := [
([pw0,pw1,pw2,pw3,pw8,pw45],[3,0,4,8,12,16,20,1,9,17,13,21,29,37,41,5,25,33,45,49,53,57,61,65,69,73,77,81,85,89,93,97,101],[33159,1675,3219,69795,132291,8973,278805,1573157,2113861,4203033,25166377,100663881,402655281,1610614865,6442455137])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p9_D8 : List StD := [
([pw0,pw1,pw18,pw2,pw3,pw8,pw45],[24,0,28,4,33,37,32,5,109,3,12,20,36,40,21,65,81,85,93,101,105,113,117],[10,10,1048579,386,386,22,2,13,9,9,9,37,1089,65,2565,2097185,32801,4194309,225792,262164,524308]),
([pw0,pw1,pw2,pw19,pw3,pw8,pw45],[24,0,3,44,48,17,33,125,52,13,8,21,129,56,60,29,81,85,41,49,57,93,101,117,121,133,137],[16777731,35,3,2566,33286,586,4273,4241,262289,524433,4313,2,33555493,67109925,8389921,75780,180228,1048904,223236,2097480,4194632]),
([pw0,pw1,pw2,pw3,pw20,pw8,pw45],[3,0,12,52,64,68,17,72,76,80,5,45,57,125,29,69,77,129,24,1,9,21,49,53,65,85,93,101,113,141,145],[525314,1091,6,6,17411,536871938,139377,2099220,1319057,12591377,143896,1073743908,268435681,16810337,70248,2,33556485,67110924,49537,70280,134238984]),
([pw0,pw1,pw2,pw3,pw8,pw21,pw45],[3,0,16,52,84,88,92,17,96,100,57,109,125,21,53,37,61,77,129,24,9,25,29,41,45,81,93,101,149,153],[2099202,2179,10243,6,6,268437506,266417,25170001,4210708,1577233,267800,98529,536887332,33185,132776,33554501,74049,67118664,2,134234124,132872]),
([pw0,pw1,pw2,pw3,pw8,pw45,pw46],[28,0,9,52,33,104,108,37,157,20,112,116,120,61,3,41,69,13,49,65,77,81,85,113,129,141,149,161,165],[263,131330,33554690,67109122,19,3,134217957,32837,262213,268468245,16777285,8414368,608416,1049105,4264,6319104,537,13320,537,71688,2]),
([pw0,pw1,pw2,pw10,pw3,pw8,pw45],[28,4,8,124,1,128,132,136,17,33,3,21,25,57,9,29,77,81,85,93,101,113,129,169,173,177],[4210714,2097436,57,7256,38040,8389145,6,6,3,3,8195,2,16777476,33554692,65541,33,33,8225,396480,524865,1049217]),
([pw0,pw1,pw2,pw3,pw12,pw8,pw45],[28,4,24,140,12,1,144,25,33,3,17,29,45,65,101,113,117,169,181,185,189],[43,33836,4280,649,2792,131369,3,3,19,3,7,262164,8197,9220,65541,2,528400,1048593,2625,261,16705]),
([pw0,pw1,pw2,pw3,pw8,pw22,pw45],[28,4,24,148,1,16,152,21,33,3,17,25,37,53,93,113,117,169,193,197,201],[27,33820,2776,10296,537,131353,3,3,3,35,7,5124,262180,4101,65541,532704,705,16705,2,1048609,261]),
([pw0,pw1,pw2,pw3,pw8,pw45,pw47],[28,52,4,24,156,1,17,160,164,168,21,25,37,85,65,81,113,129,157,3],[53,65656,2098,2098,262195,51,5,5,5,13,131073,4168,16456,11,4105,566656,3,1665,3,8961,5]),
([pw0,pw1,pw2,pw3,pw14,pw8,pw45],[24,3,8,12,172,176,1,9,180,184,188,13,29,145,25,33,41,69,173,52,49,73,77,85,89,97,101,125,129],[268435697,2134,10328,16722,21074,35922,262309,65705,134218145,1048737,65697,13,12,131591,2360325,1,8396810,16785416,135938,4752642,100668930]),
([pw0,pw1,pw2,pw3,pw8,pw23,pw45],[24,3,8,16,192,196,1,9,200,204,208,13,21,41,33,61,153,177,52,25,49,77,81,89,93,97,129,205],[67109105,2134,6482,589912,2642,19538,131237,8353,1048745,8865,8353,33031,13,12,134349829,4198666,37634,25171202,1,33619976,2377218]),
([pw0,pw1,pw2,pw3,pw8,pw45,pw48],[52,8,212,1,28,216,20,220,13,21,129,73,224,228,85,3,4,5,25,41,49,61,81,205],[131085,269,269,262157,269,269,3090,526000,1049744,1217,98449,2099234,8390658,67,19,4248096,609,8737,65,28673,3]),
([pw0,pw1,pw2,pw3,pw8,pw24,pw45],[3,12,16,232,236,240,248,1,9,17,244,13,37,33,41,185,197,28,52,5,25,57,65,73,77,81,85,93,209,213],[524697,2729,2187,1048717,3209,10441,4913,33587474,67174676,148753,2113873,4643,4194853,5665,25166433,6,6,268468290,2,536936516,134489153]),
([pw0,pw1,pw2,pw3,pw8,pw45,pw49],[52,252,1,28,256,260,129,12,37,13,93,3,20,264,25,69,89,113,5,41,49,65,161,209],[262151,519,519,16391,519,16391,4194680,524392,1048680,1121,105,197008,2140432,4369,133137,8454272,1153,9,5121,43009,129]),
([pw0,pw1,pw2,pw3,pw8,pw45,pw50],[52,268,1,28,272,16,13,101,276,280,21,37,125,129,3,20,97,5,25,41,49,61,65,213],[131079,71,71,262151,71,71,12312,528408,1052696,8337,8217,2117376,4262432,32897,18945,8455456,32897,17665,161,9,33])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p9_D7 : List StD := [
([pw51,pw0,pw1,pw2,pw3,pw8],[284,5,52,33,28,169,221,24,288,113,292,296,9,29,37,65,77,81,85,93,101,109,217,225,229,3],[35,13,65548,524300,1048588,35,4194307,35,2097155,4176,8388688,16777296,17280,33664,33958912]),
([pw0,pw1,pw18,pw2,pw3,pw8,pw24,pw45],[33,113,5,9,37,197,28,36,57,81,85,93,109,185,3,0,4,32,244,248,1,21,65,105,117,121,129,233],[33554444,1048576,8388614,4100,4100,49156,261,67108864,26,8712,1064,65608,265,18,8704,1056,393280,540673,18,4194306,18,16777219,160,2097152,2049,128,134217761,2049]),
([pw1,pw2,pw19,pw3,pw20,pw8,pw45],[68,300,125,56,53,57,3,52,5,17,13,45,129,0,72,304,33,41,85,49,69,93,101,117,133,137],[4615,4358,133126,163846,524310,4134,8192,16777225,17921,33555009,8389249,329,9,262480,65952,8192,264280,2099368,1066064,99360,4194480]),
([pw1,pw2,pw19,pw3,pw8,pw21,pw45],[88,308,125,60,45,57,3,52,17,109,13,53,129,0,96,304,33,49,81,41,61,93,101,117,133,137],[4359,4614,524310,133126,163846,4134,8192,16777537,33554441,17665,8388993,262736,585,9,66208,264280,1066064,2097328,8192,4196520,99360]),
([pw0,pw1,pw19,pw3,pw14,pw8,pw45],[24,56,129,13,29,61,3,172,180,17,33,37,85,312,125,48,52,9,41,49,57,73,77,89,97,101,133],[131085,1,67108906,904,216,9352,18437,262183,33541,524309,17413,2146,130,6224,3154944,1,4194,8388642,4944,4260608,50332688]),
([pw0,pw1,pw19,pw3,pw8,pw23,pw45],[24,60,192,61,129,13,3,17,33,137,204,65,316,21,81,125,48,52,9,41,49,57,77,89,93,97,205],[262193,1,8300,550,1188,4388,34833,524313,1049107,66705,33041,18504,2118,6,69210368,16970,8392,25166088,1,33554946,4326528]),
([pw0,pw1,pw2,pw19,pw3,pw52,pw8,pw45],[29,57,129,21,13,17,33,125,180,61,69,85,3,56,60,320,1,37,81,105,117,121,201,237,241,245,249],[10485764,524336,65536,536,256,1041,82,132,132,16777228,132,33554437,70,131072,552,32768,1057,1048610,12288,256,2049,66,262144,2057,67108874,20481,66,4194307]),
([pw0,pw1,pw2,pw3,pw52,pw8,pw45],[180,129,1,37,61,69,3,13,17,33,56,68,172,21,41,57,4,16,20,24,52,72,324,5,9,29,45,49,53,73,85,89,97,101,125],[25165830,396,8340,1,33558628,4228,267,67125266,17180459010,402653218,49666,8472,2097152,2153,536872969,4194368,1073742929,2147484689,131168,1344000,12884902432]),
([pw26,pw0,pw1,pw2,pw19,pw3,pw8,pw45],[85,125,13,57,81,17,29,129,24,33,3,0,56,328,1,21,37,105,117,121,137,189,201,245,253],[2308,386,2304,8192,32768,65,520,524294,131108,16384,1044,69,524,130,130,16777234,8388611,130,65536,1072,1048609,262184,5136,65,520,65,2097176,4194313]),
([pw26,pw0,pw1,pw2,pw3,pw8,pw45],[324,1,17,57,85,125,13,81,3,332,29,129,24,33,37,0,4,16,20,52,172,336,5,41,49,53,73,93,97,101,137,185,209],[32835,71712,4101,1048832,132368,794632,4194307,67,67,1283,67,18468,2155872416,50331696,10280,17028,1073742612,67109388,2098320,4429185160,805306392]),
([pw0,pw1,pw2,pw19,pw3,pw8,pw53,pw45],[21,57,129,13,17,29,33,125,340,61,69,81,3,56,60,344,25,65,85,105,117,121,189,237,241,245,257],[10485764,524312,65536,521,1064,256,74,132,132,16777221,33554468,132,70,131072,529,1072,32768,1048594,2049,20480,256,66,2049,12289,4194307,262144,67108898,66]),
([pw0,pw1,pw2,pw3,pw8,pw53,pw45],[61,129,25,65,3,192,204,29,60,88,13,17,33,41,21,57,4,12,20,24,52,96,9,45,49,53,81,85,89,93,97,109,205],[2151677958,3084,16437,1060,64,1060,2122,8396803,50331778,598018,45058,16921,2728,2097152,4294967880,67109265,131089,805310465,134218000,1073742272,1347584]),
([pw54,pw0,pw1,pw2,pw19,pw3,pw8,pw45],[81,125,13,57,85,17,21,129,33,3,0,8,60,348,25,29,65,105,117,121,133,189,201,241,261],[3076,130,3072,8192,65,32768,264,524294,131108,16384,69,532,268,130,130,8388611,16777234,130,65536,1048609,560,262184,65,4624,264,65,2097161,4194328]),
([pw54,pw0,pw1,pw2,pw3,pw8,pw45],[352,25,17,57,81,125,13,85,3,356,21,129,24,60,33,65,0,4,12,20,52,192,360,41,45,49,61,89,93,109,197,205,213],[65603,137248,4101,263440,2097408,1589256,536870915,67,1283,67,67,34852,25165872,1107296416,18472,67109652,33412,2147484172,4203664,402653208,4294975624]),
([pw0,pw1,pw2,pw19,pw3,pw8,pw24,pw45],[3,57,129,81,13,17,85,33,60,93,125,0,8,12,16,244,1,29,41,105,113,117,121,233,237,253,261],[20971524,524336,65536,25,81,2065,146,1028,1028,33554444,67108932,262148,134,1048576,41,97,4129,2097186,8201,16449,32769,130,264,256,522,131072,8388674,514]),
([pw1,pw2,pw3,pw20,pw8,pw21,pw45],[33,37,125,21,25,29,52,76,92,1,57,113,3,0,41,49,65,129,72,96,5,45,53,73,77,93,101,109,145,153],[133126,2113548,134234132,4227108,1081860,132101,268437514,6162,536936482,70146,25165827,8192,4520,525064,33554761,262320,400,1105,8192,67109089,1601]),
([pw0,pw1,pw2,pw10,pw3,pw20,pw8,pw45],[29,33,21,113,129,1,57,69,9,17,45,24,72,128,5,25,37,53,61,77,85,93,125,145,201,265,269],[272,520,16416,33554468,32768,161,98,67108888,4194304,1044,272,131089,82,65536,8388620,520,137,524298,1028,14336,129,66,262144,1048581,2097158,129,66,16777219]),
([pw0,pw1,pw2,pw3,pw20,pw55,pw8,pw45],[17,29,33,9,1,21,69,57,72,364,37,113,52,80,368,65,85,93,109,117,185,201,241,245,265,273],[33554456,2065,16777264,262144,512,82,148,1033,4194344,264,256,8388618,140,1025,2049,32769,67,524293,1048576,16384,65570,131108,512,66,132,66,12292,2097158]),
([pw0,pw1,pw2,pw3,pw20,pw8,pw22,pw45],[17,33,1,53,21,57,37,24,5,45,49,113,197,16,72,128,372,25,29,61,93,117,129,193,201,245,265,3],[260,2053,67108884,131072,4108,260,38,65,528,33920,33555464,4194304,34,65,2049,8388617,65,2097155,524288,4120,528,1048594,134225928,82048,34,262144,16777226,34]),
([pw0,pw1,pw2,pw3,pw20,pw52,pw8,pw45],[29,33,129,17,1,21,57,37,69,72,376,9,76,324,13,61,85,93,117,125,201,241,245,265,3],[2052,152,8388656,16384,1024,273,82,140,2097188,2052,524292,4194309,70,136,520,512,265,262154,32768,8192,65569,131106,1024,257,66,16781313,66,1048579]),
([pw56,pw0,pw1,pw2,pw3,pw8,pw45],[72,320,13,29,1,45,33,65,125,3,24,113,129,0,16,20,52,128,172,5,21,49,53,57,61,69,77,85,89,97,101,205],[8214,132097,262145,1027,16905,98305,524294,22,22,526,22,6528,1048609,6291720,8393024,16777249,33556616,2214592704,134218273,268435489,1610612808]),
([pw0,pw1,pw2,pw3,pw20,pw8,pw23,pw45],[33,129,21,65,1,153,3,57,9,69,77,145,0,24,72,204,25,29,49,61,93,113,125,137,241,257,265,277],[258,88,67108884,65536,560,4176,145,134217738,16777222,258,262146,4194306,131,2060,8264,8388648,2097152,1033,524288,100,2052,1048581,544,49216,129,131072,33554465,1025]),
([pw0,pw1,pw2,pw20,pw8,pw24,pw45],[76,232,113,129,1,21,81,3,33,197,12,244,9,17,37,57,125,52,72,5,41,45,65,73,77,85,93,141,145,185,209,213],[528408,8342,1024,147,2098,134217746,81932,536875080,33554953,3145768,98568,8388,4194949,268451876,25166084,262211,3,1073774912,1024,2147484161,67242016]),
([pw0,pw1,pw2,pw3,pw20,pw8,pw57,pw45],[33,113,129,29,21,57,1,9,17,72,244,37,85,380,25,81,93,117,137,233,241,245,265],[132,258,4194384,16384,4168,1024,97,2054,1048596,132,2097164,132,37,2050,258,262154,258,131075,32768,4120,8192,65553,520,1024,33,512,524297,33]),
([pw0,pw1,pw2,pw3,pw8,pw57,pw45],[113,129,232,1,21,29,244,33,128,9,17,25,37,57,125,3,20,24,52,72,96,5,41,45,49,53,65,73,77,81,85,93,101,141,145,153,209,213],[2097674,33805,2060,2060,64,8589934604,20483,12582930,50331682,131842,24706,17179873297,34426847265,34049,402653313,1610612788,1048576,70866960464,524288,141733920864,336000]),
([pw58,pw0,pw1,pw2,pw3,pw8,pw45],[72,384,25,17,76,21,1,69,125,3,24,33,129,0,20,52,128,232,388,5,37,45,49,57,73,77,81,97,141,145,209,281],[8262,66561,1545,35,131073,49153,524294,526,70,70,268435462,1052936,2097185,4195216,8395008,536870945,2147745944,50333704,67108881,1073741857,134217872]),
([pw0,pw1,pw2,pw10,pw3,pw8,pw21,pw45],[21,33,113,129,29,25,57,61,9,17,53,24,128,1,37,45,69,77,81,101,109,125,153,189,269,285],[264,516,1048608,161,33554480,8192,98,16777228,2097152,32777,1048,264,74,16384,133,4194324,516,131078,129,1040,6144,66,262145,129,8388611,65536,524306,66]),
([pw0,pw1,pw2,pw3,pw12,pw8,pw21,pw45],[17,33,25,45,29,57,24,37,41,53,65,109,113,185,12,96,128,392,1,21,69,101,117,129,189,241,285,3],[2052,4101,8204,2052,67108884,262144,38,129,33554696,8388608,528,65856,34,129,1025,1025,4097,4194307,524288,8200,134234120,16777226,528,163904,34,1048576,2097170,34]),
([pw0,pw1,pw2,pw3,pw8,pw21,pw59,pw45],[17,21,33,9,25,29,61,57,96,396,37,113,52,100,400,5,81,101,117,137,189,197,241,245,285,289],[33554456,2065,82,16777264,32768,512,148,1033,4194314,8388648,264,256,140,67,524321,2049,1025,262149,65538,66,66,1048582,2097152,16384,131108,512,132,12292]),
([pw0,pw1,pw2,pw3,pw14,pw8,pw21,pw45],[33,129,29,37,25,145,3,57,9,61,77,153,0,96,128,180,1,21,41,69,101,113,125,133,245,249,285,293],[258,88,560,4176,67108884,65536,145,134217738,262146,4194306,16777222,258,131,8388648,2097152,2060,16456,1033,131072,100,544,33554465,2052,41024,1025,524288,1048581,129]),
([pw0,pw1,pw2,pw3,pw8,pw21,pw53,pw45],[21,33,129,17,25,57,29,61,65,96,404,9,92,352,13,69,81,101,117,125,189,241,245,285,3],[2052,280,145,8388688,16384,1024,50,268,2097157,4194372,2052,524292,38,137,264,520,512,262154,65537,129,16781313,1048579,32768,8192,131138,1024,34,34]),
([pw60,pw0,pw1,pw2,pw3,pw8,pw45],[96,344,13,21,129,25,53,33,37,49,3,128,113,0,12,20,24,52,192,29,41,45,57,61,69,73,77,81,89,93,97,109],[8230,68112,262145,17417,2051,163841,2147483654,38,1038,38,38,4880,3145752,524369,4194960,8392968,16777281,100663680,134218817,805306504,1073741889]),
([pw0,pw1,pw2,pw3,pw21,pw24,pw45],[92,232,113,129,25,29,85,3,33,37,185,16,244,9,17,57,125,52,96,41,53,73,77,81,93,109,149,153,197,209,213],[33562648,16534,147,2048,4146,67108882,66060,8389641,268443720,1572904,98568,1669,16580,134218276,6291716,262211,2048,536871937,3,1073774912,16912416]),
([pw0,pw1,pw2,pw3,pw8,pw21,pw57,pw45],[33,113,129,21,29,57,9,17,25,96,408,37,81,384,1,85,93,101,117,137,241,245,285],[68,130,4360,4194576,16384,1024,289,2054,1048588,2097172,68,68,37,2050,524306,130,130,262147,4104,520,512,65545,32768,8192,131089,1024,33,33]),
([pw61,pw0,pw1,pw2,pw3,pw8,pw45],[96,380,1,17,92,29,25,61,125,3,24,33,37,129,0,20,52,128,232,412,5,41,53,57,73,77,85,89,141,153,213],[16454,132097,1545,262145,35,98305,1048582,526,70,70,268435462,12552,2098064,4194337,8399104,528536,536870945,50333704,67108881,134217872,1073741857]),
([pw0,pw1,pw2,pw3,pw14,pw8,pw45,pw46],[29,129,37,13,145,69,33,9,41,61,77,157,32,52,180,1,21,57,73,85,89,97,113,125,133,245,293,297],[130,2060,536,2056,41,134217800,32768,67108870,258,8388610,33554435,258,130,16777236,4194304,37,1092,262148,65536,524305,1048592,528,33,1088,28672,2097153,33,131072]),
([pw0,pw1,pw2,pw3,pw8,pw23,pw45,pw46],[21,129,65,13,61,153,33,9,49,69,77,157,32,52,1,29,57,81,89,97,113,125,137,205,241,277,297],[130,2060,25,552,2056,67108936,16384,33554438,16777219,258,2097154,258,130,21,4194340,1048576,1092,8388612,131073,17,262145,17,32768,524320,544,1088,12288,65536]),
([pw0,pw1,pw2,pw3,pw8,pw24,pw45,pw46],[113,129,33,81,85,141,37,32,52,112,9,17,41,157,209,213,1,21,57,65,117,149,253,261,297],[1026,2049,8232,2097184,8224,16777252,65536,67,4194314,8388626,4098,4098,1026,65,524289,65,1048581,2049,528,131072,16392,16392,512,32788,32784,388,384,262144]),
([pw0,pw1,pw2,pw10,pw3,pw8,pw24,pw45],[57,113,129,1,197,185,24,32,132,25,33,81,85,93,157,173,128,5,21,37,77,105,121,125,177,233,237,269,301],[71303172,270532610,131080,520,520,16392,16392,134217734,8388608,2084,4116,196,1029,524288,32770,16777218,32770,1048579,2080,4112,65600,1025,272,262144,8225,256,33554449,8321]),
([pw62,pw0,pw1,pw2,pw3,pw8,pw45],[24,392,140,32,21,29,113,17,25,57,85,157,96,368,65,101,117,133,185,189,3],[5,5,193,8212,1053730,522,7,133,22,2308,2316,67,23,3,3,131075,16449,65545,263216,524314,33320]),
([pw63,pw0,pw1,pw2,pw3,pw8,pw45],[392,24,25,113,49,81,41,45,1,57,69,0,32,52,17,29,33,65,73,97,101,157,181,209,3],[16779525,81,11,161,2,12289,7,16398,165,34052,2163204,11,81,81,19,4194307,131082,262154,161,8388641,1574400]),
([pw64,pw0,pw1,pw2,pw3,pw8,pw45],[24,372,148,32,29,21,113,1,17,57,157,12,37,81,93,117,137,197,201,3],[5,5,321,534562,22,522,7,261,1156,22,1164,67,3,23,3,4161,65539,32777,131122,16936,262154]),
([pw65,pw0,pw1,pw2,pw3,pw8,pw45],[372,24,1,113,41,85,49,53,25,57,61,0,32,52,17,21,33,37,73,89,93,157,193,213,3],[16779525,81,11,2,161,12289,7,16398,34052,165,2163204,11,81,81,19,131082,4194307,262154,161,1574400,8388641]),
([pw0,pw1,pw2,pw3,pw8,pw24,pw45,pw47],[1,113,37,57,85,81,160,5,25,93,125,157,185,197,24,32,21,33,41,65,73,101,105,129,305],[129,4194307,257,257,2049,2049,129,6,4128,8208,263168,16778248,8388608,6,524290,6,1048578,6,80,65536,552,4128,64,2097176,8208,520,49152,131072]),
([pw0,pw1,pw2,pw3,pw14,pw52,pw8,pw45],[180,129,1,29,77,172,13,41,61,69,184,332,416,17,21,37,57,85,121,125,133,201,237,245,249,3],[4456450,68,68,33,1,44,68,3,130,3,524290,8388618,130,1081600,8192,4096,513,17,16384,2048,131073,16777473,32,513,17,33555464,65552,2097176]),
([pw66,pw0,pw1,pw2,pw3,pw8,pw45],[180,172,17,21,69,109,3,24,32,33,49,129,157,16,52,1,25,37,45,53,57,73,85,89,97,101,113],[32771,385,67108867,131,8273,16641,65570,7,11,4130,4130,131077,262153,527376,1052160,15,85,2097157,4194377,8388617,50332176]),
([pw0,pw1,pw3,pw14,pw8,pw23,pw45],[24,1,57,129,61,65,69,184,200,25,37,41,3,33,77,180,204,5,9,49,73,89,97,125,145,153,157,205],[393226,16777746,4642,33555010,5634,67117062,2073,8388649,524361,3081,10252,1,4560,66832,2097428,32992,416,134234148,1,4194500,1065988]),
([pw0,pw1,pw2,pw14,pw8,pw24,pw45],[240,184,1,37,129,57,61,81,3,13,85,12,25,33,125,24,180,244,5,9,41,73,77,89,93,145,173,185,197,209,213],[786452,781,4484,5382,33555012,8740,67108873,134234256,268436498,1081424,24624,2048,267,131145,2097161,65667,3,541065376,2048,1073742850,25165920]),
([pw0,pw1,pw2,pw3,pw14,pw8,pw67,pw45],[129,1,69,77,37,13,33,180,420,25,41,61,85,125,424,65,81,121,133,157,237,249,257,261,293],[1179649,34,34,514,514,524290,34,16777233,1025,8193,8388613,8193,1025,264208,32768,4116,256,88,65536,4100,16384,2099208,132,256,72,128,4194316,72]),
([pw0,pw1,pw2,pw3,pw8,pw67,pw45],[240,1,37,57,129,61,69,13,32,33,41,65,93,185,197,3,0,24,52,180,204,244,5,9,25,49,73,89,97,101,125,145,153,157,173],[12582930,32903,2147483810,4311744578,8590032898,650,17179869189,9264,33570896,1073873168,1560,2053,2053,2097152,67108869,24673,1048576,134221864,524288,805306440,266504]),
([pw68,pw0,pw1,pw2,pw3,pw8,pw45],[180,25,37,81,24,29,33,129,145,3,32,428,1,13,49,0,52,184,240,5,9,21,53,57,65,73,89,101,113,173,185],[37379,1041,268435477,2097177,262145,66561,1572994,8711,267,6178,10306,536870917,1073741833,4210848,8405184,269,16777221,33554437,265,67108873,134349408]),
([pw0,pw1,pw2,pw3,pw14,pw8,pw45,pw69],[129,1,29,37,77,13,25,69,180,432,41,61,93,24,128,436,85,121,125,133,205,209,237,245,257,293],[4325377,34,34,66,66,34,66,33554441,1025,262145,8388613,1025,24577,526344,1048576,140,4120,512,2097152,65540,6160,32768,132,272,512,16777236,132,256]),
([pw0,pw1,pw2,pw3,pw14,pw8,pw45,pw50],[129,1,37,13,61,97,41,52,25,73,89,101,213,16,32,180,440,21,29,33,113,121,125,133,201,237,293,309,313,3],[35651585,10,10,258,258,10,10,67108869,65,4194305,402653185,65,65,8388628,1048576,4132,516,516,131072,4144,1040,1040,536879136,18560,98432,16779296,262144,524288]),
([pw0,pw1,pw2,pw3,pw8,pw23,pw53,pw45],[204,21,129,25,77,13,61,192,49,69,200,356,444,17,29,57,65,81,121,125,137,189,237,241,257,3],[4456452,40,74,40,129,1,40,5,8388614,260,5,524292,260,66,1114624,8192,4096,17,131074,66,33555458,2097170,16384,2048,16777729,128,17,32784]),
([pw70,pw0,pw1,pw2,pw3,pw8,pw45],[204,192,17,29,61,5,3,24,32,33,41,129,157,12,52,1,25,45,53,57,65,81,89,93,97,113,205],[65539,385,33554435,8273,131,16641,32802,7,4130,11,4130,1048581,134160,262153,527872,85,15,67108869,2097225,12583440,16777225]),
([pw0,pw1,pw2,pw3,pw23,pw24,pw45],[240,200,1,13,65,129,57,69,85,3,81,16,33,125,24,204,244,5,9,41,77,93,97,153,177,185,197,205,209,213],[393252,541,1550,780,8388748,4172,16777233,33555490,67117344,540832,12384,531,2048,65681,134217745,33027,2048,268436482,3,537919808,6291648]),
([pw0,pw1,pw2,pw3,pw8,pw23,pw67,pw45],[129,1,77,13,61,65,33,204,448,49,69,81,125,200,452,25,37,85,121,137,157,237,249,253,257,277],[2359297,10,10,32770,10,1048578,10,33554465,8388625,513,4097,4097,513,2096,525344,65536,256,100,2064,8320,128,4194324,131072,16384,16778244,256,68,68]),
([pw71,pw0,pw1,pw2,pw3,pw8,pw45],[204,200,1,65,24,456,21,25,153,173,3,32,13,33,129,197,0,52,5,9,45,57,61,73,97,113,125,189],[66693,2065,33554457,4194307,19,133121,802820,5133,230,421,12324,521,1048642,33025,69230592,515,521,8388617,32771,134218818,16777473]),
([pw0,pw1,pw2,pw3,pw8,pw23,pw45,pw49],[129,1,65,13,89,49,69,52,25,93,97,205,209,12,32,204,460,21,29,33,113,121,125,137,189,237,277,317,321,3],[35651585,10,10,258,10,10,258,67108869,402653185,33,4194305,33,33,4116,8388676,1048576,2052,2052,4112,536879120,16777744,131072,262144,1088,1088,17024,98432,524288]),
([pw0,pw1,pw2,pw3,pw8,pw23,pw45,pw72],[129,1,21,13,65,77,61,204,464,49,69,101,24,128,468,25,73,81,121,125,137,213,237,241,249,277],[4456449,10,10,32770,10,10,10,33554449,8388613,513,524289,513,12289,84,1049616,65536,2096,256,131076,68,16777252,68,2097152,3104,16384,160,256,128]),
([pw73,pw0,pw2,pw3,pw8,pw45],[24,52,472,1,9,161,476,480,21,25,41,85,37,49,81,129,157,225,229,277,293,325,3],[32797,4145,1041,8209,1041,2097197,526,526,65550,1048609,524321,35,4213184,131394,264322]),
([pw0,pw1,pw2,pw3,pw8,pw24,pw45,pw48],[129,1,85,73,81,157,52,216,25,77,125,205,209,213,3,24,32,228,236,244,21,33,41,113,117,121,237,253,261,329,333],[100663297,1610612738,258,258,34,34,34,1025,134217745,268435461,4194305,1025,278529,2072,2060,49160,16777736,8388608,132,1048576,4112,4112,128,8196,8196,66112,655424,2097152]),
([pw0,pw1,pw2,pw3,pw8,pw24,pw57,pw45],[113,129,244,232,25,33,37,85,92,1,9,17,41,93,484,488,21,57,65,81,117,233,253,261],[1026,2049,528,528,12,4,56,67,4718594,8388738,4098,1026,4098,65,262145,65,2049,1048609,384,65536,16384,8196,256,32768,2097284,8,8196,131104]),
([pw28,pw0,pw1,pw2,pw3,pw8,pw45],[244,232,21,29,37,157,24,32,492,33,125,3,52,1,13,45,53,57,73,77,113,121,129,145,153,169,209,213],[8195,193,2129,7,11,4225,2099234,16418,7,11,33554722,5243920,32773,65545,132864,8388613,16777225,786960,15,67108869,134217737]),
([pw0,pw1,pw2,pw3,pw8,pw24,pw74,pw45],[1,113,244,33,37,85,157,152,496,25,41,57,81,93,240,500,45,65,105,117,233,253,261,273,337,341,345,3],[25165825,262147,513,513,65,65,65,18,35655680,71303200,1028,4,3080,18,131074,18,134234114,524298,160,65536,256,12292,128,32768,1048612,256,8196,2056]),
([pw0,pw1,pw2,pw3,pw8,pw24,pw67,pw45],[129,1,244,37,13,81,85,200,504,33,41,65,77,93,508,25,61,121,125,157,233,237,253,261,293],[2228225,18,18,32770,18,524290,18,16777225,4194337,8388673,1025,262145,1025,2088,2056,12,4,4616,192,65536,256,8228,128,16384,1048644,256,8196,4608]),
([pw75,pw0,pw1,pw2,pw3,pw8,pw45],[244,81,157,153,24,240,57,113,129,145,32,200,1,33,125,3,0,52,512,5,9,13,17,21,69,89,97,117,185,197],[102405,1041,2049,8388627,2065,132097,1573124,6291588,519,16777229,12356,278944,268435459,536870921,24896,515,41,134250720,515,33554435,67108873]),
([pw0,pw1,pw2,pw3,pw8,pw24,pw45,pw76],[113,129,25,276,37,93,41,85,244,516,1,81,157,232,520,65,89,105,121,237,253,261,301,349,3],[786434,4325377,1028,1028,4100,4100,16785412,19,1050626,2097282,66,66,66,17,32769,17,8388641,17,136,65536,2088,512,8,168,16384,288,512,256]),
([pw77,pw0,pw1,pw2,pw3,pw8,pw45],[52,432,25,460,61,129,24,1,29,209,524,13,65,113,125,0,4,244,5,49,69,85,317,3],[32901,82016,1,594,10617096,75,262149,2053,133,133,2053,28704,4195378,525600,9,530,1061120,9,530,19,9]),
([pw78,pw0,pw1,pw2,pw3,pw8,pw45],[52,460,25,81,113,129,1,89,24,13,29,37,125,0,4,5,33,49,53,65,69,101,185,3],[8261,20768,8390930,138,1,2162691,32773,517,69,69,517,6192,4194346,394272,3,154,1573904,3,138,11,3]),
([pw79,pw0,pw1,pw2,pw3,pw8,pw45],[52,440,1,21,129,213,24,25,69,13,37,113,125,0,4,244,528,5,29,41,45,61,81,309,3],[8325,20560,1,21004298,262242,67,131077,517,133,133,517,7184,1572888,8454194,3,2100232,290,3,298,3,259]),
([pw80,pw0,pw1,pw2,pw3,pw8,pw45],[52,440,1,85,113,129,25,97,24,13,21,65,125,0,4,5,33,37,41,45,61,93,197,3],[8261,20768,8390930,1,138,2162691,32773,517,69,69,517,6192,787488,4194346,3,1180688,154,3,138,3,11])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p9_D6 : List StD := [
([pw51,pw0,pw1,pw2,pw3,pw8,pw24],[113,169,9,33,5,37,197,296,81,85,185,21,65,93,105,109,129,225],[18,65548,41,1288,584,8200,18,16387,18,32770,18,37,1284,580,131076,33,4097,33,192,2048,128]),
([pw28,pw1,pw18,pw2,pw3,pw8,pw45],[5,37,93,21,121,29,113,33,81,492,532,1,61,85,109,117,129,137,169,233,337,353,357],[1048593,3073,67,4105,16385,133,65536,82,2097176,4194352,148,66,264,8224,262660,66,131106,32774,264,140,524324]),
([pw1,pw19,pw3,pw20,pw8,pw23,pw45],[1,129,33,21,65,17,137,49,57,13,29,61,69,93,105,117,121,125,133,237,241,257,273,3],[4194307,1048586,589826,130,131074,130,17,17,17,17,261,2048,8388680,262184,8204,4160,16928,260,1024,2097220,32804]),
([pw26,pw1,pw2,pw19,pw20,pw8,pw45],[13,29,33,129,21,17,57,81,85,125,37,61,105,117,121,133,137,201,241,245,361],[262168,32816,1048576,2065,274,84,520,520,16393,524298,76,1024,4129,65570,8228,129,258,68,131,69,131078]),
([pw1,pw2,pw3,pw20,pw8,pw53,pw45],[33,129,21,29,65,1,17,93,12,25,57,61,69,85,105,113,117,121,133,237,241,245,257,273,305,325,361,3],[33554450,1048582,655362,2097162,8388642,16777219,262164,16464,88,32768,65553,2048,134217740,67108900,133,4104,288,1537,8192,4194313,161]),
([pw54,pw1,pw2,pw3,pw20,pw8,pw45],[17,33,129,1,21,25,57,65,85,360,13,29,61,93,113,117,121,133,157,201,241,261,273,361],[4194316,16393,8388632,262184,2048,74,133,1048596,65572,2097412,70,131089,161,129,32771,4096,784,8210,1056,98,524546]),
([pw1,pw2,pw19,pw20,pw8,pw24,pw45],[125,13,21,85,17,33,81,1,129,3,29,57,93,105,113,117,121,133,233,237,241,261,361],[257,257,589825,2097161,1048581,257,16384,8210,536,131092,32816,66,648,4194436,2208,74,70,66,1024,262184,4132]),
([pw1,pw2,pw19,pw3,pw8,pw57,pw45],[125,21,29,33,17,25,13,129,1,57,536,61,69,85,93,105,113,117,121,133,137,233,237,241,245],[129,129,8388611,16777221,4456449,129,65536,524306,1048596,32848,131096,290,292,1120,552,8198,2048,16394,4096,2097164,584]),
([pw58,pw1,pw2,pw19,pw3,pw8,pw45],[57,129,21,25,13,17,1,33,69,125,388,29,61,81,93,105,113,117,121,133,201,237,241,309],[2359298,32816,88,4116,2048,145,514,522,4194310,8388866,131,65536,524324,1312,131105,72,72,137,8196,16389,1048833]),
([pw1,pw19,pw3,pw14,pw8,pw21,pw45],[37,129,29,33,133,17,25,41,57,13,21,61,69,101,105,117,121,125,137,181,237,245,249,293,3],[8388611,130,131074,2097158,1114114,130,524305,65,69,65,265,1024,16777236,2064,4194328,262180,16928,32808,4096,8204,264]),
([pw1,pw2,pw3,pw52,pw8,pw21,pw45],[33,129,21,29,37,25,1,17,57,536,61,69,81,101,113,117,121,137,237,241,245,249,289,305,325,365,3],[16777234,524294,4194338,1048586,327682,8388611,148,16384,131096,144,32785,4096,67108876,1028,2097157,33554472,608,289,2048,8201,321]),
([pw26,pw1,pw2,pw3,pw8,pw21,pw45],[17,33,129,1,25,29,37,57,81,336,13,21,69,101,113,117,121,137,157,189,245,253,289,365],[4194324,16401,2048,8388656,262168,146,69,2097412,1048612,65548,134,65,131105,73,32771,800,1032,524546,4096,8226,138]),
([pw54,pw1,pw2,pw19,pw3,pw21,pw45],[13,21,33,129,29,17,57,81,85,125,65,69,105,117,121,133,137,189,241,245,365],[524312,65584,1048576,146,2065,84,520,520,262154,16393,76,1024,32802,4129,8228,130,257,68,259,131078,69]),
([pw1,pw2,pw19,pw3,pw21,pw24,pw45],[125,13,29,81,17,33,85,129,25,93,3,21,57,105,113,117,121,137,237,245,253,365,369],[129,129,1048585,327681,524293,129,16384,1048,8210,131092,32816,4195336,66,2097412,4384,74,2048,552,70,66,548]),
([pw61,pw1,pw2,pw19,pw3,pw8,pw45],[57,129,1,29,13,17,25,33,61,125,412,21,69,85,105,113,117,121,137,189,233,237,245,317],[2228226,16432,84,2048,4120,145,514,518,8388866,4194314,131,32768,1312,262184,65569,68,68,133,8200,524545,1048585]),
([pw26,pw0,pw1,pw19,pw14,pw8,pw45],[29,129,17,33,133,85,125,57,81,1,21,61,105,117,121,181,201,237,245,373],[526352,82,32768,1044,49,152,147458,512,4356,33,136,66,66,262147,66,260,33,136,37,8204,65545]),
([pw0,pw1,pw3,pw14,pw8,pw53,pw45],[33,129,65,61,69,17,57,37,41,540,1,21,25,29,85,105,117,121,133,181,237,245,249,257,3],[1179650,262152,32804,8208,1024,4161,258,38,2097170,258,67,2048,16777240,524424,4194313,36,644,65541,16384,8388625,65]),
([pw54,pw0,pw1,pw3,pw14,pw8,pw45],[13,33,129,37,65,133,17,57,85,360,1,21,25,29,41,113,117,121,181,201,249,261,293,373],[1033,4194316,262184,32792,8192,138,131077,8388641,81,4097,131,16388,84,2097412,134,2048,800,1048610,80,65554,524546]),
([pw0,pw1,pw19,pw14,pw8,pw24,pw45],[57,81,129,17,85,13,33,37,133,3,1,29,41,105,117,121,181,233,237,249,261,293,373],[294916,1024,8202,560,4194592,97,2097284,14,1048596,4100,69,10,656,65920,65,10,10,16387,2048,131089,524545]),
([pw0,pw1,pw19,pw3,pw8,pw67,pw45],[57,129,61,69,17,33,37,13,0,1,21,29,65,85,105,117,121,125,133,137,181,237,249,253,257,261,293],[2162690,512,262148,524296,16528,161,67108930,8388614,33554442,131074,35,1048644,4168,272,33,8204,1024,4194309,2048,16777225,32785]),
([pw68,pw0,pw1,pw19,pw3,pw8,pw45],[125,133,13,17,33,65,29,129,428,37,1,21,57,81,105,113,117,121,137,201,245,249,253,373],[16396,137,32808,2058,262144,65560,131077,1024,8388614,324,276,129,4194307,1048641,129,546,544,4144,8194,2097170,524368]),
([pw0,pw1,pw3,pw52,pw8,pw23,pw45],[33,129,61,37,137,1,57,65,21,540,25,29,49,81,105,117,121,193,237,241,249,257,277,325,377,3],[327682,260,1024,16777264,16424,97,524294,4194434,4098,8388618,67,8192,33554452,260,1048581,131216,648,65,2048,2097169,32777]),
([pw26,pw0,pw1,pw3,pw8,pw23,pw45],[1,129,33,13,37,65,137,81,57,336,17,21,29,49,113,117,121,189,193,253,257,277,325,377],[9,2097186,2048,262240,16432,292,65539,9,8388673,9,9,524418,8194,4194322,262,704,1040,131204,4096,1048644,32788]),
([pw54,pw0,pw1,pw19,pw3,pw23,pw45],[21,129,33,137,17,81,125,57,85,25,29,69,105,117,121,189,193,237,241,377],[526344,74,65536,41,1048,140,147458,512,33,4368,132,66,262147,66,66,33,272,132,33,32773,8212]),
([pw0,pw1,pw19,pw3,pw23,pw24,pw45],[17,57,129,81,13,85,137,33,65,93,3,1,21,41,105,117,121,193,237,253,277,377],[327684,2048,1048,16401,2097232,146,1048836,524300,37,8196,134,1288,33,131392,130,41,4096,522,97,32771,578]),
([pw71,pw0,pw1,pw19,pw3,pw8,pw45],[125,137,13,17,33,37,456,21,129,65,1,29,57,85,105,113,117,121,133,189,241,257,261],[16396,265,32808,262144,2058,65560,131077,1024,196,70,84,257,1048705,4194307,257,544,546,4144,8194,524432,2097170]),
([pw26,pw0,pw1,pw2,pw52,pw8,pw45],[29,33,129,1,21,37,57,61,81,85,0,336,105,117,121,137,201,241,245,325,341,381,385],[152,131092,144,1024,529,82,16396,4136,2097152,521,74,524324,1048836,262149,70,4194304,32801,8226,2305,66,65539]),
([pw81,pw0,pw1,pw2,pw19,pw3,pw45],[33,69,129,21,57,17,13,29,61,85,125,1,37,105,117,121,237,241,245,389,393],[130,262150,130,514,514,19,98308,8288,2048,328,17,1028,1028,131084,21,4096,296,16417,524296,17,1048585]),
([pw0,pw1,pw2,pw52,pw8,pw24,pw45],[33,129,37,61,1,17,57,81,85,16,3,21,25,29,105,113,117,121,233,237,241,249,261,341,397],[655362,16420,4096,16778256,2072,81,38,8388738,4194562,1048586,67,32768,1284,36,65541,640,648,65,8192,262401,2097161]),
([pw0,pw1,pw2,pw3,pw82,pw52,pw45],[33,129,29,37,61,17,57,1,69,336,428,21,85,105,113,117,121,125,157,237,241,245,249,257],[589826,8232,2064,388,262144,193,42,1048594,2097158,131074,67,40,268,16384,32777,4116,512,4194321,1024,8388613,65]),
([pw0,pw1,pw2,pw3,pw8,pw83,pw45],[33,129,29,37,61,17,57,1,428,456,21,25,85,105,113,117,121,125,137,157,237,241,245,249,257],[1114114,8232,1040,2180,524288,193,42,2097170,4194310,131074,67,40,262156,16384,32777,4116,512,8388625,256,16777221,65]),
([pw81,pw0,pw1,pw2,pw3,pw8,pw45],[25,125,57,65,81,1,17,129,21,33,29,117,121,133,201,241,249,309,313,401],[33,130,72,272,1024,516,4099,73,33,33,517,130,32786,393218,130,8216,72,2060,272,65556,540676]),
([pw81,pw0,pw1,pw2,pw3,pw52,pw45],[33,129,1,21,69,37,57,29,61,544,85,105,117,121,125,241,245,249,281,325,389,405],[148,65554,144,1048,512,81,8198,2084,268,2097152,69,524322,32778,16386,67,296,262144,4129,1048576,131081,65]),
([pw81,pw0,pw1,pw2,pw3,pw45],[57,69,125,281,389,405,17,33,129,1,13,21,29,5,9,37,41,45,53,61,73,77,85,89,93,97],[4642,262406,4170,4196370,33554563,24612,1128,2608,1185,332,196628,389,557080,3145737,25165841]),
([pw0,pw1,pw2,pw3,pw8,pw84,pw45],[33,37,129,17,25,29,81,1,57,456,21,85,105,117,121,125,137,189,237,245,253,257,409],[278532,4106,144,144,144,273,14,1048644,524324,32772,261,10,65570,10,8195,4194400,1600,131137,2048,2097185,257]),
([pw85,pw0,pw1,pw2,pw3,pw8,pw45],[1,125,13,37,57,81,85,129,17,360,21,25,29,33,65,117,121,189,201,253,261],[5,130,264,1024,4096,8208,65539,5,5,2049,5,130,524322,1048642,130,264,16392,32792,608,131120,262224]),
([pw54,pw0,pw1,pw2,pw3,pw53,pw45],[21,33,129,25,29,57,65,69,81,85,0,360,105,117,121,133,189,241,245,281,325,345,405],[152,262164,144,273,1024,50,16396,4168,265,4194304,42,1048644,131077,2097668,38,32833,524288,8258,2561,65539,34]),
([pw86,pw0,pw1,pw2,pw19,pw8,pw45],[33,61,129,29,57,17,13,21,69,81,125,105,117,121,237,241,245,381,385,389,393],[130,32774,130,514,514,19,24580,2144,131072,328,17,1028,1028,65548,21,262144,296,4129,524296,17,1048585]),
([pw0,pw1,pw2,pw3,pw53,pw24,pw45],[33,129,65,69,17,25,57,81,85,12,93,3,1,21,29,105,113,117,121,237,245,253,345,369],[786434,32788,8390688,4096,16424,97,22,2097282,4194562,1048586,67,2180,65536,20,131077,896,8192,1025,776,65,1033]),
([pw0,pw1,pw2,pw87,pw8,pw53,pw45],[33,129,61,65,17,57,69,21,360,456,25,29,81,105,113,117,121,125,157,237,241,245,249,257],[589826,8216,132,2112,262144,1057,26,1048582,2097218,131074,35,140,24,16384,32777,4100,512,4194309,256,8388673,33]),
([pw86,pw0,pw1,pw2,pw8,pw53,pw45],[33,129,29,61,57,65,17,21,548,69,81,105,117,121,125,237,241,245,257,381,385,389],[136,65546,136,1036,256,25,40962,2144,516,524288,17,98,131078,16386,19,100,1048576,4129,2097152,262149,17]),
([pw86,pw0,pw1,pw2,pw3,pw8,pw45],[1,125,37,57,85,17,25,129,29,33,21,117,121,137,189,245,257,317,321,413],[65,130,36,1024,272,520,4099,37,65,65,521,130,393218,32786,130,36,8212,2060,272,540680,65560]),
([pw86,pw0,pw1,pw2,pw8,pw45],[57,61,125,381,385,389,17,33,129,13,21,25,29,9,45,49,53,65,69,77,81,89,97,101,417,421],[3082,16646,1106,1052706,2097283,16785420,600,6184,649,340,98340,389,393264,34078737,12582945]),
([pw0,pw1,pw2,pw3,pw88,pw8,pw45],[33,37,129,61,85,17,25,57,1,65,428,21,29,81,105,117,121,125,201,237,241,249,261,409],[589828,16418,2056,320,320,193,38,1048588,131076,4194324,133,34,514,514,32771,8192,8388632,2097161,5136,129,262161]),
([pw56,pw1,pw2,pw3,pw8,pw21,pw45],[21,129,25,33,285,13,1,61,29,57,17,65,69,77,101,121,161,241,245,249,425,3],[1048582,1024,133,276,100,524,67586,131075,262162,32802,522,129,272,96,8200,2097169,129,524297,4096,16408,96]),
([pw60,pw1,pw2,pw3,pw20,pw8,pw45],[129,1,13,29,33,265,25,21,57,69,17,37,61,77,93,121,161,241,245,257,337,3],[1048579,1024,162,70,522,274,67585,131105,32773,262153,273,160,68,520,8208,4096,2097192,16432,68,68,524312]),
([pw1,pw2,pw20,pw21,pw24,pw45],[1,33,37,125,21,369,57,113,0,16,92,9,129,3,52,5,17,41,45,73,77,93,141,145,429,433],[4236,16779304,34825,393240,4170,8356,73733,8388756,1572870,1537,816,33554530,1281,4194371,2113554]),
([pw58,pw0,pw1,pw2,pw3,pw22,pw45],[17,25,33,53,21,57,309,1,37,45,113,552,5,29,61,93,117,129,245],[130,262216,1033,16408,10248,44,4098,1027,130,130,38,321,592,131072,100,257,257,65541,528,32788,36]),
([pw81,pw0,pw1,pw2,pw3,pw20,pw45],[33,69,129,1,17,21,57,29,37,9,61,85,93,241,245,265,281,405,437],[138,16390,130,2082,130,67,524,280,32808,131072,73,276,8228,516,69,304,65552,262161,1024,4129,65]),
([pw0,pw1,pw2,pw3,pw8,pw89,pw45],[21,113,129,13,29,77,1,65,33,41,61,25,69,85,121,233,237,241,245,249,301],[81924,1048586,73,2072,72,72,134,131077,262164,516,516,1027,130,130,290,8209,1025,524321,4096,32816,288]),
([pw56,pw0,pw1,pw2,pw8,pw24,pw45],[1,33,129,61,81,21,57,85,65,16,13,17,25,29,77,113,121,161,233,241,249,253,261,397,3],[4113,2097172,2048,528,56,82,65541,1025,25165825,41,67,131332,4194436,524300,70,33152,40,16386,8192,262274,1048586]),
([pw0,pw1,pw2,pw20,pw23,pw24,pw45],[21,33,129,65,1,57,85,3,204,9,77,81,145,25,113,241,257,265,277,345,397,441],[516,152,8192,1048720,131089,50,262156,516,524356,32773,38,2097288,16384,4105,1034,2368,2305,34,4161,1026,65539]),
([pw90,pw0,pw1,pw2,pw3,pw8,pw45],[13,69,129,1,41,57,61,29,21,17,33,77,85,121,245,249,257],[9,20,512,320,130,1056,8197,9,9,131,9,20,20,16390,20,320,130,2080,4162,32864,65570]),
([pw0,pw1,pw2,pw91,pw3,pw8,pw45],[33,129,37,21,25,69,1,17,57,81,428,29,105,113,117,121,125,201,237,241,249,309,445],[294914,4228,80,80,80,273,134,65538,524298,2097186,259,8192,132,4194340,16389,520,3104,257,520,1048585,131105]),
([pw61,pw0,pw1,pw2,pw12,pw8,pw45],[1,17,33,45,317,29,57,25,53,65,113,556,21,69,117,129,233,241,353,449],[137,131096,1034,6152,8232,76,262161,1027,129,129,69,524306,32768,304,84,514,514,16390,288,68,65572]),
([pw0,pw1,pw2,pw14,pw21,pw24,pw45],[33,61,129,37,25,57,3,9,77,81,145,180,1,29,85,113,133,245,249,293,341,369,453],[132,88,2097232,4096,1042,49,524300,1049092,132,131078,37,32768,4194376,65546,265,18944,8194,257,1026,33,262147]),
([pw86,pw0,pw1,pw2,pw8,pw21,pw45],[33,61,129,29,385,57,17,21,9,25,69,81,101,137,241,245,285,381,457],[130,16390,130,2058,130,35,260,80,66056,131072,33,84,32780,260,37,8216,80,262161,1024,4105,33]),
([pw0,pw1,pw2,pw3,pw92,pw8,pw45],[29,113,129,13,21,77,1,37,33,41,69,25,61,85,93,121,237,241,245,257,301],[98308,1048586,88,72,2057,72,134,131092,516,262149,516,130,130,1027,290,4096,8209,16432,1025,288,524321]),
([pw60,pw0,pw1,pw2,pw3,pw24,pw45],[25,33,129,69,85,29,57,37,81,93,12,1,13,17,21,77,113,121,161,245,253,261,369,3],[2065,2097172,8192,1040,56,82,131077,4097,12582913,41,67,262276,1048836,524300,70,65920,40,32770,16384,514,522]),
([pw0,pw1,pw2,pw93,pw3,pw8,pw45],[33,129,61,65,1,29,17,25,57,85,456,21,105,113,117,121,125,189,237,245,257,317,461],[294914,4168,144,144,144,273,74,65538,2097158,524322,259,8192,4194316,72,16393,3076,544,257,548,131077,1048609]),
([pw0,pw1,pw2,pw3,pw8,pw94,pw45],[9,17,25,21,85,33,37,41,81,113,157,1,29,57,117,189,193,201,237,241,261,381,465],[262149,518,2097164,4194324,3076,1028,67,524297,1048593,129,129,66,65554,514,16418,280,264,32808,4096,131120,8224]),
([pw0,pw95,pw1,pw2,pw3,pw8,pw45],[21,33,113,29,49,1,9,57,65,81,101,25,69,105,117,121,133,189,241,265,273,301,465],[2048,1081344,2105348,524321,4194344,162,80,260,513,4104,1026,84,262161,88,130,65541,260,16390,513,131075,1034]),
([pw0,pw1,pw2,pw3,pw96,pw8,pw45],[1,9,17,29,33,81,37,41,85,113,157,21,25,57,117,137,189,201,237,245,253,405,417],[262147,517,4194337,5121,2097161,1025,70,1048610,130,524298,130,68,516,32780,16404,2048,296,65584,264,8208,131096]),
([pw0,pw97,pw1,pw2,pw3,pw8,pw45],[29,33,61,113,41,9,21,25,57,85,93,1,37,105,117,121,137,201,245,285,289,301],[2048,1081344,2105352,68,524417,386,48,4104,68,513,1026,56,52,262161,258,76,65545,16394,517,1030,131075]),
([pw81,pw0,pw1,pw2,pw3,pw14,pw45],[33,129,405,29,37,1,57,61,69,77,13,17,21,41,85,121,125,133,245,249,293],[36,262154,280,16520,264,73,32774,1028,36,36,69,1048594,8194,65538,67,131216,2048,529,4096,524417,513]),
([pw0,pw1,pw2,pw3,pw8,pw98,pw45],[37,129,33,61,69,17,25,9,21,157,1,29,65,85,93,117,241,249,257,261,305,469],[130,33,264,2097232,1600,576,35,65546,524306,130,1048582,33,4113,33,32773,8216,264,131084,2048,262164,16388]),
([pw66,pw0,pw1,pw3,pw8,pw23,pw45],[9,21,93,17,33,137,37,61,69,129,1,29,49,65,117,193,241,257,3],[1024,513,130,33056,72,8212,513,130,288,72,20,65539,4097,73,21,262178,130,22,2048,131108,16396]),
([pw66,pw0,pw1,pw2,pw8,pw24,pw45],[9,17,93,85,21,33,37,81,61,129,16,1,29,117,157,233,241,261,369,3],[2048,513,66,1160,400,164,513,66,278536,272,36,67,131081,65553,37,524298,66,8198,4096,32780,52]),
([pw70,pw0,pw1,pw3,pw14,pw8,pw45],[9,69,17,33,133,29,37,41,61,65,129,1,21,25,113,117,169,181,245,249,257,349,3],[8192,1025,131344,16452,98,2097224,1025,272,516,34,67592,129,517,262147,129,4096,4194322,524312,38,32780,1048586]),
([pw0,pw1,pw14,pw23,pw24,pw45],[1,37,57,129,61,441,24,125,16,200,25,33,77,157,3,5,9,41,73,89,93,145,173,473,477],[98313,17441,17411,2105361,10245,8388776,4194442,131160,2188,770,368,16781348,578,266246,1572884]),
([pw99,pw0,pw1,pw2,pw3,pw8,pw45],[9,17,29,33,21,37,93,69,61,129,1,85,117,241,245,257],[1024,513,34,272,132,72,513,34,272,132,72,35,8209,16389,73,34,134,4106,2068,88,32780]),
([pw0,pw100,pw1,pw2,pw3,pw8,pw45],[33,37,129,61,17,29,57,1,65,81,428,21,25,69,105,117,121,125,201,237,241,245,249,469],[4096,589828,16402,2056,8388768,193,131076,258,520,9216,65,22,1048588,2097188,69,18,258,32771,520,4194313,262177]),
([pw68,pw0,pw1,pw2,pw3,pw45,pw50],[25,125,65,81,129,1,37,201,13,61,97,560,29,33,121,253,257,393,437],[33,18,68,520,66688,7168,16387,257,33,257,33,18,32778,18,18,68,262276,68,131208,520,8192]),
([pw86,pw0,pw1,pw2,pw8,pw23,pw45],[21,33,129,381,57,61,69,13,65,77,17,25,29,49,81,121,125,137,241,257,277],[41,262149,33,16449,33,19,32780,136,2056,136,26,1048836,8196,65540,22,131392,1024,514,4096,524354,514]),
([pw0,pw1,pw2,pw3,pw101,pw8,pw45],[17,29,129,1,33,61,37,9,85,157,21,25,93,117,137,245,249,253,257,301,305,405,481],[132,524297,4194344,2568,2097162,520,69,131108,132,32774,1048596,97,65,16387,8209,1024,290,65584,258,4112,262162]),
([pw70,pw0,pw1,pw2,pw3,pw24,pw45],[9,17,33,29,65,85,1,69,81,93,129,157,12,21,25,117,233,245,253,305,397,3],[16384,1025,18,4128,168,65572,1025,18,1050688,136,2116,19,262401,131081,524293,2097410,18,32774,8192,516,524]),
([pw0,pw102,pw1,pw2,pw3,pw8,pw45],[33,37,69,129,17,21,25,57,29,85,456,1,61,105,117,121,125,189,237,241,245,257,481],[2048,294920,8210,4194400,324,193,65544,18,5120,516,129,26,524328,1048588,137,18,262,16387,548,131105,2097157]),
([pw71,pw0,pw1,pw2,pw8,pw45,pw49],[1,125,37,85,129,25,65,189,13,69,89,564,21,33,121,249,261,393,457],[33,18,68,520,33920,7168,16387,257,33,257,33,18,65546,18,18,68,262276,68,131208,520,8192]),
([pw73,pw0,pw2,pw3,pw8,pw24,pw45],[129,161,25,221,41,476,1,157,225,293,21,37,49,85,117,121,229,237,277,485,489],[163841,2051,17,4097,17,17,1572866,68,68,132,132,514,262146,514,16394,8224,1024,264,32,65544,264]),
([pw75,pw0,pw1,pw3,pw8,pw45,pw48],[129,157,1,61,69,41,81,117,73,85,113,512,568,25,33,121,261,349,437,457],[6,33,72,528,131456,5376,32771,6,8194,6,6,33,65553,33,3073,72,524424,72,262288,528,16384]),
([pw0,pw1,pw2,pw103,pw3,pw8,pw45],[21,29,57,129,13,37,61,77,125,1,69,85,113,121,157,169,193,237,241,245,249,257,293,381,405,493],[139272,33554480,16912,8388625,16777234,32788,4194344,264,262153,524298,268,4096,97,65570,164,65,1026,132,2051,1048581,2097158]),
([pw104,pw0,pw1,pw3,pw8,pw24,pw45],[57,113,161,25,33,37,85,572,1,93,41,45,65,81,105,157,233,253,261,301,485,489],[540674,38,34,4098,34,19,3145732,264,264,32776,17,139268,262212,1028,21,192,2048,513,128,65601,513]),
([pw0,pw105,pw1,pw2,pw3,pw8,pw45],[29,33,61,129,113,21,57,1,9,17,69,25,85,117,125,157,241,245,249,257],[32768,264,528,36,2177,194,264,528,36,1025,66,16392,65548,131081,74,52,1041,8210,4101,262150,524291]),
([pw106,pw1,pw2,pw3,pw8,pw24,pw45],[1,37,129,576,113,169,85,25,41,81,93,157,65,253,261,273,381,497],[32773,19,129,129,2049,2049,22,8708,16452,260,260,18,4098,18,131106,72,65536,1568,8,104,1064]),
([pw0,pw1,pw2,pw3,pw8,pw107,pw45],[61,113,129,1,77,65,85,13,81,125,25,29,93,105,121,189,201,237,253,261,301,385,481,501],[147460,1056770,4194313,1032,136,136,38,262149,524356,516,516,2097155,34,34,8388626,321,257,32785,2048,65616,4112]),
([pw0,pw1,pw2,pw108,pw3,pw8,pw45],[129,1,37,61,93,25,49,69,101,29,81,113,117,121,133,157,237,253,293,329],[73729,524294,34,34,34,32770,262149,65,131081,65,65,2048,16396,644,4116,1032,640,272,1032,280,400]),
([pw0,pw1,pw2,pw3,pw109,pw8,pw45],[113,129,69,25,77,37,81,1,13,85,125,21,93,105,121,189,201,237,253,261,281,301,501],[147458,2105345,136,264,136,264,35,262210,1026,524294,1026,33,33,1048581,4194321,2048,580,32848,516,4112,65556]),
([pw0,pw1,pw2,pw110,pw3,pw8,pw45],[129,1,65,69,93,25,41,61,21,77,85,113,117,121,137,157,201,237,261,277,329],[139265,1048582,34,34,34,32770,524293,65,65,262153,65,2048,388,16396,4116,384,1032,528,1032,656,65560])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p9_D5 : List StD := [
([pw1,pw19,pw20,pw23,pw24,pw45],[1,21,33,129,85,57,65,69,81,105,117,121,193,237,241,257,273,305,325],[65545,10248,262168,16394,131084,65,65,4099,37,784,130,36,146,1044,32774]),
([pw1,pw2,pw20,pw53,pw24,pw45],[33,129,1,21,65,12,17,57,69,105,113,117,121,237,241,257,273,305,325,369],[262162,12290,65542,16394,131075,592,1024,88,2065,36,264,524417,36,133,32777]),
([pw1,pw19,pw14,pw21,pw24,pw45],[33,37,81,129,133,57,17,25,61,85,105,113,117,121,181,237,245,249,293,305,325],[262154,1048588,40968,65560,524297,2054,130,16402,35,1540,68,4101,272,33,131089]),
([pw1,pw2,pw52,pw21,pw24,pw45],[21,33,129,37,369,1,17,57,536,61,105,113,117,121,237,241,249,305,325,365,505],[262156,1048596,24580,32773,131078,2048,1096,73,4106,304,524305,146,513,162,65539]),
([pw0,pw1,pw14,pw53,pw24,pw45],[33,61,129,441,37,57,580,1,17,25,105,117,121,133,181,237,245,249,293,325,369],[36868,1049600,128,8194,545,524300,262164,65542,37,88,266,2057,16402,33,131075]),
([pw0,pw1,pw52,pw23,pw24,pw45],[33,37,129,61,17,57,441,580,1,21,105,117,121,193,237,241,249,509,513],[20484,131072,1042,520,289,262212,22,32780,37,194,8264,33,18,2051,65545]),
([pw56,pw1,pw2,pw21,pw24,pw45],[13,129,1,33,61,369,21,57,17,77,121,161,241,249,509,517],[32802,256,37,112,168,18434,1027,4114,138,5,80,520,5,5,8216]),
([pw60,pw1,pw2,pw20,pw24,pw45],[13,129,1,33,265,369,21,57,17,37,77,121,161,241,257,337],[32774,256,37,84,140,4610,2051,8210,138,33,80,1032,33,33,16408]),
([pw66,pw0,pw1,pw23,pw24,pw45],[9,17,93,21,33,37,61,129,1,117,241,441],[256,129,34,72,2068,129,34,72,20,35,1033,21,34,518,28]),
([pw70,pw0,pw1,pw14,pw24,pw45],[9,17,33,133,37,441,61,129,1,25,113,117,169,245,249,305,349],[512,129,1042,88,65556,129,34,72,4356,35,8201,32773,42,2054,16396])]
def p9_D4 : List StD := []
theorem p9_I4 : LevelN true p9_T 4 p9_D4 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p9_C5x0 : levelOK true p9_T p9_t 4 (p9_D4.map Prod.fst) ((p9_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p9_I5 : LevelN true p9_T 5 p9_D5 := levelStep p9_B p9_W p9_I4 (chunks 32 p9_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p9_C5x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p9_C6x0 : levelOK true p9_T p9_t 5 (p9_D5.map Prod.fst) ((p9_D6.drop (0*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p9_C6x1 : levelOK true p9_T p9_t 5 (p9_D5.map Prod.fst) ((p9_D6.drop (1*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p9_C6x2 : levelOK true p9_T p9_t 5 (p9_D5.map Prod.fst) ((p9_D6.drop (2*32)).take 32) = true := by decide +kernel
theorem p9_I6 : LevelN true p9_T 6 p9_D6 := levelStep p9_B p9_W p9_I5 (chunks 32 p9_D6 3 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p9_C6x0
  · exact p9_C6x1
  · exact p9_C6x2
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p9_C7x0 : levelOK true p9_T p9_t 6 (p9_D6.map Prod.fst) ((p9_D7.drop (0*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p9_C7x1 : levelOK true p9_T p9_t 6 (p9_D6.map Prod.fst) ((p9_D7.drop (1*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p9_C7x2 : levelOK true p9_T p9_t 6 (p9_D6.map Prod.fst) ((p9_D7.drop (2*32)).take 32) = true := by decide +kernel
theorem p9_I7 : LevelN true p9_T 7 p9_D7 := levelStep p9_B p9_W p9_I6 (chunks 32 p9_D7 3 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p9_C7x0
  · exact p9_C7x1
  · exact p9_C7x2
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p9_C8x0 : levelOK true p9_T p9_t 7 (p9_D7.map Prod.fst) ((p9_D8.drop (0*32)).take 32) = true := by decide +kernel
theorem p9_I8 : LevelN true p9_T 8 p9_D8 := levelStep p9_B p9_W p9_I7 (chunks 32 p9_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p9_C8x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p9_C9x0 : levelOK true p9_T p9_t 8 (p9_D8.map Prod.fst) ((p9_D9.drop (0*32)).take 32) = true := by decide +kernel
theorem p9_I9 : LevelN true p9_T 9 p9_D9 := levelStep p9_B p9_W p9_I8 (chunks 32 p9_D9 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p9_C9x0
  ))
theorem p9_L : LowN true p9_R p9_T 10 := lowSearch p9_B p9_I9 (by decide +kernel)
def p10_T : Nat := 0xeeeaece8eeeaece8eeeaece8eeeaece8eeeaece8eeeaece8eeeaece8eeeaece8
def p10_R : List Nat := [0, 1, 2, 3, 4]
def p10_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,2,10),(4,1,17)]
theorem p10_B : baseOK p10_T p10_R p10_E = true := by decide +kernel
def p10_Z : List SliceD := [(pw5,5,[0, 1, 2, 4])]
theorem p10_Y : ∀ s ∈ p10_Z, SliceN true p10_R p10_T s := by
  unfold p10_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p10_B p4_B p4_L (by decide +kernel),by simp⟩
def p10_C : List (Nat × List Nat) := [(0,[])]
def p10_t : Tabs := (p10_C.map (mkCut true p10_Z),[(5,4),(6,4),(3,2),(3,1),(6,2),(5,1),(10,2),(13,12)],[],[[]])
theorem p10_W : TabsP true p10_R p10_T p10_t := ⟨cutsGood p10_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p10_D5 : List StD := [
([pw0,pw1,pw2,pw3,pw8],[0,1,5,17,25,9,13,21,29],[102,170,275,3,204,5,5,25,9,17])]
def p10_D4 : List StD := []
theorem p10_I4 : LevelN true p10_T 4 p10_D4 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_C5x0 : levelOK true p10_T p10_t 4 (p10_D4.map Prod.fst) ((p10_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p10_I5 : LevelN true p10_T 5 p10_D5 := levelStep p10_B p10_W p10_I4 (chunks 32 p10_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p10_C5x0
  ))
theorem p10_L : LowN true p10_R p10_T 6 := lowSearch p10_B p10_I5 (by decide +kernel)
def p11_T : Nat := 0xfffefeeefffefeeefffefeeefffefeeefffefeeefffefeeefffefeeefffefeee
def p11_R : List Nat := [0, 1, 2, 3, 4]
def p11_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,8,12),(3,4,12),(4,4,20)]
theorem p11_B : baseOK p11_T p11_R p11_E = true := by decide +kernel
def p11_Z : List SliceD := [(pw4,5,[1, 2, 3, 4])]
theorem p11_Y : ∀ s ∈ p11_Z, SliceN true p11_R p11_T s := by
  unfold p11_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p11_B p3_B p3_L (by decide +kernel),by simp⟩
def p11_C : List (Nat × List Nat) := [(0,[])]
def p11_t : Tabs := (p11_C.map (mkCut true p11_Z),[(1,0),(2,0)],[],[[]])
theorem p11_W : TabsP true p11_R p11_T p11_t := ⟨cutsGood p11_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p11_D5 : List StD := [
([pw0,pw1,pw2,pw3,pw8],[0,1,5],[7,3,3,3,5,5,5,1,1,1])]
def p11_D4 : List StD := []
theorem p11_I4 : LevelN true p11_T 4 p11_D4 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p11_C5x0 : levelOK true p11_T p11_t 4 (p11_D4.map Prod.fst) ((p11_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p11_I5 : LevelN true p11_T 5 p11_D5 := levelStep p11_B p11_W p11_I4 (chunks 32 p11_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p11_C5x0
  ))
theorem p11_L : LowN true p11_R p11_T 6 := lowSearch p11_B p11_I5 (by decide +kernel)
def p12_T : Nat := 0xeeeaece0eeeaece0eeeaece0eeeaece0eeeaece0eeeaece0eeeaece0eeeaece0
def p12_R : List Nat := [0, 1, 2, 3, 4]
def p12_E : List (Nat × Nat × Nat) := [(0,4,5),(1,4,6),(2,1,5),(3,2,10),(4,1,17)]
theorem p12_B : baseOK p12_T p12_R p12_E = true := by decide +kernel
def p12_Z : List SliceD := []
theorem p12_Y : ∀ s ∈ p12_Z, SliceN true p12_R p12_T s := by
  intro s h
  cases h
def p12_C : List (Nat × List Nat) := []
def p12_t : Tabs := (p12_C.map (mkCut true p12_Z),[(5,4),(10,9),(6,4),(6,2),(5,0),(10,3),(10,2),(17,1),(17,0),(5,1),(10,0),(17,3),(5,9),(6,18),(17,9)],[],[[]])
theorem p12_W : TabsP true p12_R p12_T p12_t := ⟨cutsGood p12_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p12_D4 : List StD := [
([pw0,pw1,pw2,pw3,pw8],[1,9,13,25,29,5,17,21,33,37,41,45,49,53,57],[35,69,137,273,518,1034,2066,4108,8212,16408])]
def p12_D3 : List StD := []
theorem p12_I3 : LevelN true p12_T 3 p12_D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p12_C4x0 : levelOK true p12_T p12_t 3 (p12_D3.map Prod.fst) ((p12_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p12_I4 : LevelN true p12_T 4 p12_D4 := levelStep p12_B p12_W p12_I3 (chunks 32 p12_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p12_C4x0
  ))
theorem p12_L : LowN true p12_R p12_T 5 := lowSearch p12_B p12_I4 (by decide +kernel)
def p13_T : Nat := 0xfefefeeefefafc88fefefeeefefafc88fefefeeefefafc88fefefeeefefafc88
def p13_R : List Nat := [0, 1, 2, 3, 4, 5]
def p13_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,8,12),(3,2,10),(4,1,17),(5,1,33)]
theorem p13_B : baseOK p13_T p13_R p13_E = true := by decide +kernel
def p13_Z : List SliceD := [(pw7,6,[0, 1, 5, 3, 4]),(pw2,6,[3, 4, 0, 1, 5]),(pw5,7,[4, 0, 1, 5, 2]),(pw9,7,[3, 1, 0, 5, 2]),(pw29,7,[0, 2, 3, 1, 4]),(pw4,5,[1, 2, 3, 4, 5]),(pw17,5,[0, 2, 4, 3, 5])]
theorem p13_Y : ∀ s ∈ p13_Z, SliceN true p13_R p13_T s := by
  unfold p13_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p13_B p10_B p10_L (by decide +kernel),mkSlice (w:=4) p13_B p11_B p11_L (by decide +kernel),mkSlice (w:=0) p13_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p13_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p13_B p7_B p7_L (by decide +kernel),mkSlice (w:=0) p13_B p12_B p12_L (by decide +kernel),mkSlice (w:=0) p13_B p12_B p12_L (by decide +kernel),by simp⟩
def p13_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(2,[262]),(5,[]),(2,[263]),(2,[260]),(3,[260]),(4,[384]),(6,[]),(2,[261]),(4,[385]),(3,[261]),(3,[263]),(4,[386]),(3,[262]),(4,[387]),(2,[261,404])]
def p13_t : Tabs := (p13_C.map (mkCut true p13_Z),[(17,16),(10,8),(3,2),(3,1),(12,8),(13,9),(13,5),(10,2),(17,1),(20,4),(33,1),(34,2),(22,18),(22,6),(33,5),(17,9),(33,9),(34,18),(10,9),(37,36),(12,5),(38,36),(20,6),(12,4),(37,5),(7,6),(19,18),(7,5),(3,0),(3,9),(25,24),(26,24),(20,16),(44,40),(26,18),(25,9),(44,36),(41,9),(52,36),(50,18),(3,18),(33,0),(34,0),(3,5),(41,8),(11,9),(50,16)],[],[[]])
theorem p13_W : TabsP true p13_R p13_T p13_t := ⟨cutsGood p13_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p13_D8 : List StD := [
([pw0,pw1,pw2,pw3,pw8,pw45],[0,4,8,12,16,17,33,41,25,29,37,45,1,5,9,13,21,49,53,57,61,65,69,3],[8450048,65571,772,1096,2192,131107,772,262216,2192,39,1131,524467,1048588,2097172,4194328])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p13_D7 : List StD := [
([pw111,pw0,pw1,pw2,pw3,pw8,pw45],[24,32,36,40,44,3,20,1,5,77,85,0,4,28,29,33,37,41,61,65,69,73,81,89,93,97],[65,8193,6145,99,37,41,2097169,641,4194307,133,521,1296,274,8388628,1048,16793602,98308,33685512,262150,524298,1048588]),
([pw0,pw1,pw18,pw2,pw3,pw8,pw45],[24,44,48,52,9,13,33,56,21,25,41,29,45,49,53,0,4,17,37,61,65,69,73,93,97,101,105,109,3],[4194355,2,33554705,2581,67108945,5145,1,134225954,2598,16610,5162,229632,8389124,262336,268436488,2564,24896,16778504,524420,1048588,2097352]),
([pw112,pw0,pw1,pw2,pw3,pw8,pw45],[24,20,44,60,64,25,33,41,32,9,29,53,0,4,48,5,45,49,61,65,69,85,97,101,113],[260,16385,12289,291,73,145,16777733,8389121,35,73,145,2260996,1062,2124,65684,1058,2120,4194448,262154,524306,1048600]),
([pw113,pw0,pw1,pw2,pw3,pw8,pw45],[44,28,68,72,29,45,53,24,48,13,25,33,0,4,1,5,21,41,61,65,69,77,97,109,113],[257,32769,12289,275,69,41,16777857,2179200,1042,2116,131112,8389121,19,69,41,1042,2116,4194344,262150,524298,1048588])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p13_D6 : List StD := [
([pw0,pw1,pw2,pw114,pw8,pw45],[44,1,5,17,29,37,45,77,85,25,33,129,21,41,97,117,121,125,133,137,141,145,149,153,157],[32775,4234,66066,1186,8386,261,261,131077,261,2584,3112,278600,1572912,6291536,25165920]),
([pw0,pw1,pw2,pw3,pw115,pw45],[24,1,5,17,33,41,93,49,77,85,29,53,45,97,121,125,133,137,141,145,149,153,157,161],[8388615,259,16387,259,259,652,1604,34836,4644,1224,2200,73768,393296,1572960,6291504]),
([pw0,pw1,pw2,pw3,pw8,pw116],[24,44,1,5,29,33,41,77,85,129,17,37,73,93,97,121,125,133,137,141,145,149,153,157],[4111,133,32773,133,133,266,266,65546,266,9744,3616,148032,786480,3145808,12583008]),
([pw51,pw0,pw1,pw18,pw2,pw3,pw8],[21,29,33,9,45,37,93,17,13,41,76,25,53,61,73,165,169,173],[536,528,1024,145,82,52,16648,32768,137,2058,44,65536,131329,66,4100,129,66,36,67,37,8198]),
([pw51,pw0,pw1,pw2,pw3,pw8],[17,37,45,93,165,169,29,33,49,9,13,21,41,25,53,97,101,105,109,137,141,149,157,177,181,185],[4628,5156,34821,2097228,4194438,1584,67601,8396824,131218,262433,16777320,33570850,329,387,1572874])]
def p13_D5 : List StD := []
theorem p13_I5 : LevelN true p13_T 5 p13_D5 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p13_C6x0 : levelOK true p13_T p13_t 5 (p13_D5.map Prod.fst) ((p13_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p13_I6 : LevelN true p13_T 6 p13_D6 := levelStep p13_B p13_W p13_I5 (chunks 32 p13_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p13_C6x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p13_C7x0 : levelOK true p13_T p13_t 6 (p13_D6.map Prod.fst) ((p13_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p13_I7 : LevelN true p13_T 7 p13_D7 := levelStep p13_B p13_W p13_I6 (chunks 32 p13_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p13_C7x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p13_C8x0 : levelOK true p13_T p13_t 7 (p13_D7.map Prod.fst) ((p13_D8.drop (0*32)).take 32) = true := by decide +kernel
theorem p13_I8 : LevelN true p13_T 8 p13_D8 := levelStep p13_B p13_W p13_I7 (chunks 32 p13_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p13_C8x0
  ))
theorem p13_L : LowN true p13_R p13_T 9 := lowSearch p13_B p13_I8 (by decide +kernel)
def p14_T : Nat := 0xfeeafcc0feeafcc0feeafcc0feeafcc0feeafcc0feeafcc0feeafcc0feeafcc0
def p14_R : List Nat := [0, 1, 2, 3, 4]
def p14_E : List (Nat × Nat × Nat) := [(0,16,17),(1,4,6),(2,2,6),(3,2,10),(4,1,17)]
theorem p14_B : baseOK p14_T p14_R p14_E = true := by decide +kernel
def p14_Z : List SliceD := [(pw0,5,[4, 2, 3, 1])]
theorem p14_Y : ∀ s ∈ p14_Z, SliceN true p14_R p14_T s := by
  unfold p14_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=1) p14_B p3_B p3_L (by decide +kernel),by simp⟩
def p14_C : List (Nat × List Nat) := [(0,[])]
def p14_t : Tabs := (p14_C.map (mkCut true p14_Z),[(17,16),(6,4),(19,18),(7,5),(6,2),(21,20),(7,3),(10,2),(25,24),(11,3)],[],[[]])
theorem p14_W : TabsP true p14_R p14_T p14_t := ⟨cutsGood p14_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p14_D5 : List StD := [
([pw0,pw1,pw2,pw3,pw8],[0,1,5,17,29,9,13,21,25,33,37],[102,394,1554,1,1,5,5,25,9,17])]
def p14_D4 : List StD := []
theorem p14_I4 : LevelN true p14_T 4 p14_D4 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p14_C5x0 : levelOK true p14_T p14_t 4 (p14_D4.map Prod.fst) ((p14_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p14_I5 : LevelN true p14_T 5 p14_D5 := levelStep p14_B p14_W p14_I4 (chunks 32 p14_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p14_C5x0
  ))
theorem p14_L : LowN true p14_R p14_T 6 := lowSearch p14_B p14_I5 (by decide +kernel)
def p15_T : Nat := 0xfffefeeefff8f8a8fffefeeefff8f8a8fffefeeefff8f8a8fffefeeefff8f8a8
def p15_R : List Nat := [0, 1, 2, 3, 4, 5]
def p15_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,4,12),(4,4,20),(5,1,33)]
theorem p15_B : baseOK p15_T p15_R p15_E = true := by decide +kernel
def p15_Z : List SliceD := [(pw17,7,[0, 2, 3, 4, 5]),(pw5,7,[2, 0, 1, 5, 4]),(pw9,7,[2, 0, 1, 5, 3]),(pw29,7,[0, 2, 3, 4, 1]),(pw4,6,[1, 2, 3, 4, 5]),(pw113,5,[5, 3, 4, 2]),(pw30,5,[0, 2, 3, 4]),(pw7,6,[3, 1, 0, 5, 4]),(pw31,4,[2, 3, 4]),(pw3,6,[2, 4, 0, 1, 5]),(pw8,6,[2, 3, 0, 1, 5]),(pw45,6,[0, 1, 2, 3, 4]),(pw117,5,[4, 1, 0, 5]),(pw118,5,[3, 1, 0, 5]),(pw32,5,[1, 2, 3, 4]),(pw119,5,[2, 1, 0, 5]),(pw120,4,[0, 1, 5])]
theorem p15_Y : ∀ s ∈ p15_Z, SliceN true p15_R p15_T s := by
  unfold p15_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p15_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p15_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p15_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p15_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p15_B p14_B p14_L (by decide +kernel),mkSlice (w:=2) p15_B p3_B p3_L (by decide +kernel),mkSlice (w:=2) p15_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p15_B p14_B p14_L (by decide +kernel),mkSlice (w:=0) p15_B p1_B p1_L (by decide +kernel),mkSlice (w:=8) p15_B p11_B p11_L (by decide +kernel),mkSlice (w:=16) p15_B p11_B p11_L (by decide +kernel),mkSlice (w:=32) p15_B p11_B p11_L (by decide +kernel),mkSlice (w:=8) p15_B p3_B p3_L (by decide +kernel),mkSlice (w:=16) p15_B p3_B p3_L (by decide +kernel),mkSlice (w:=32) p15_B p3_B p3_L (by decide +kernel),mkSlice (w:=8) p15_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p15_B p1_B p1_L (by decide +kernel),by simp⟩
def p15_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(1,[261]),(2,[261]),(9,[]),(10,[]),(1,[262]),(2,[262]),(11,[]),(0,[128]),(1,[128]),(12,[]),(3,[128]),(0,[129]),(1,[129]),(13,[]),(2,[129]),(14,[]),(0,[130]),(1,[131]),(0,[257]),(15,[]),(0,[258]),(0,[385]),(1,[517]),(0,[513]),(1,[389]),(2,[389]),(1,[390]),(2,[390]),(1,[257]),(1,[393]),(2,[393]),(0,[261]),(16,[]),(3,[261]),(0,[262]),(3,[262]),(0,[389]),(1,[513]),(3,[389]),(0,[390]),(3,[390]),(0,[517]),(0,[393]),(3,[393]),(0,[521]),(0,[525]),(0,[514]),(3,[513]),(1,[261,406]),(2,[261,406]),(0,[128,277]),(0,[128,405]),(0,[128,533]),(0,[258,405]),(0,[386,277]),(1,[389,278]),(2,[389,278]),(0,[261,406]),(3,[261,406]),(0,[389,278]),(3,[389,278])]
def p15_t : Tabs := (p15_C.map (mkCut true p15_Z),[(34,32),(3,2),(3,1),(12,8),(5,4),(5,1),(12,4),(11,10),(25,17),(20,4),(19,18),(25,9),(34,2),(33,32),(33,1),(38,36),(14,10),(11,9),(14,6),(19,17),(22,6),(20,16),(44,40),(38,6),(44,36),(41,9),(52,36),(49,17),(7,6),(24,16),(24,8),(3,6),(37,36),(3,9),(3,17),(13,9),(21,17),(33,9),(33,17),(5,0),(3,10),(41,40),(24,9),(19,1),(5,17),(3,18),(49,48),(12,10),(34,6),(24,17),(19,2),(5,9),(20,0),(5,36),(33,0),(42,10),(50,18),(22,18),(7,1),(42,40),(26,18),(50,48),(26,10),(56,48),(52,48),(34,36),(37,1),(3,0),(56,40),(34,0),(38,4),(5,6),(12,36),(11,2),(11,1),(12,0),(20,36),(7,2),(24,40),(12,6),(20,6),(24,18),(20,18),(24,10),(33,16),(33,8),(7,4),(11,8),(19,16),(34,18),(34,10),(25,1),(13,1),(14,2),(44,32),(24,0),(24,32),(22,4),(14,4),(12,2),(3,16),(19,0),(3,8),(11,0),(34,4)],[],[[]])
theorem p15_W : TabsP true p15_R p15_T p15_t := ⟨cutsGood p15_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p15_D9 : List StD := [
([pw0,pw1,pw2,pw3,pw8,pw45],[3,0,4,8,12,1,25,33,37,45,49,5,9,13,17,21,29,41,53,57,61,65,69,73,77,81,85,89,93,97,101,105,109],[6179,59393,65733,131849,787473,3145763,12582951,50331691,5171,8389,67109641,402654225,717,1610612821,6442451225])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p15_D8 : List StD := [
([pw0,pw1,pw18,pw2,pw3,pw8,pw45],[20,0,16,24,5,57,3,32,36,40,13,25,117,121,12,28,29,37,41,85,93,101,109,113],[22,2,8388629,65557,262165,61,6,3,3,3,3,33921,129,129,16457,7488,664128,1048616,15168,2097192,4194344]),
([pw112,pw0,pw1,pw2,pw3,pw8,pw45],[16,24,0,57,3,33,45,113,52,56,25,4,8,28,44,48,5,9,13,21,29,37,41,49,85,93,101,109],[4,131077,532497,18465,36929,11,7,65665,1048705,4194433,11,6,6,6,8388614,263472,18874960,33554442,1904,67108874,134217738]),
([pw121,pw0,pw1,pw2,pw3,pw8,pw45],[28,16,5,65,3,20,64,9,24,68,72,25,53,85,0,4,8,12,32,44,48,60,76,1,13,17,21,29,41,57,69,77,89,97,109,117,125],[33554435,16657,67108865,557073,1114129,2228497,4102,68719476739,134217734,268435462,4102,16777225,1073742048,2147483872,8388832,8201,8201,4294967305,34359741952,8589938176,17721196544]),
([pw0,pw1,pw2,pw19,pw3,pw8,pw45],[20,72,80,1,28,88,33,57,113,84,96,21,45,32,92,9,25,37,49,61,93,117,121,125,129,133,137,141,145,149,153],[33037,8390929,16,66371,151841,16785793,524301,32781,33554511,67113005,32781,1,134285330,268568624,1059984,2097730,4214816,271488,66114,536872642,1073763488]),
([pw122,pw0,pw1,pw2,pw3,pw8,pw45],[32,28,72,100,1,88,49,9,17,33,13,25,45,57,85,4,8,104,21,37,61,93,133,137,149,153,157,3],[2,153,134479873,33285,69665,8257,153,67109123,773,4385,8257,1048603,4194333,8388665,153,19462,541730,2097219,133636,16777285,33554529]),
([pw123,pw0,pw1,pw2,pw3,pw8,pw45],[72,20,61,117,88,96,37,32,93,25,5,9,53,57,0,17,21,33,45,157,3],[1081345,16391,3,521,81,417,7174,589827,131083,262226,13346,135,15,86,10374,521,81,417,521,297,368]),
([pw0,pw1,pw2,pw3,pw20,pw8,pw45],[72,32,108,1,112,21,4,29,37,45,49,20,96,9,13,33,57,65,85,89,137,153,161,165],[8334,16547,4227075,65,914,8455298,131117,77,2061,1051164,9230,16417,262177,273,524323,2,65,32835,273,5123,2101778]),
([pw124,pw0,pw1,pw2,pw3,pw8,pw45],[72,20,4,96,112,116,69,21,57,8,88,9,33,37,169,173,177,3],[4,2147,131,4101,132609,265,106,131,5,16402,266,227,5,32882,106,21,65553,137,5,5,8472]),
([pw0,pw1,pw2,pw3,pw8,pw21,pw45],[88,20,120,1,21,96,112,124,41,45,9,13,25,33,57,32,49,133,149,177,181,185,189,193],[1294,2323,12738,1049091,65,2113826,4194335,139342,15,1038,1038,2065,524817,2065,8388657,4737,4289,286944,2,16929,98337]),
([pw125,pw0,pw1,pw2,pw3,pw8,pw45],[96,88,32,9,112,21,37,41,57,4,5,45,49,121,133,189,197,201,205,209,3],[1025,13,35,1049105,2051,259,13,35,65681,131075,4481,32774,16412,14,13,262194,524386,5,8258,5,5]),
([pw0,pw1,pw2,pw3,pw8,pw45,pw46],[32,96,128,1,129,3,132,136,9,25,117,121,0,5,13,37,49,53,57,61,69,77,85,165,185,213],[269,131089,8388625,16777233,33816593,8193,524301,1048589,2097165,269,4141,18016,4229280,3,3,3808,3,3,3,3,65537]),
([pw126,pw0,pw1,pw2,pw3,pw8,pw45],[32,1,49,129,3,9,33,45,88,112,140,144,25,4,5,13,21,37,53,57,61,69,77,85,93,165,185,217,221,225],[16385,35,65809,8769,897,524289,35,262153,33554441,67108873,134217741,1048579,2097155,4194307,35,37968,8521872,16777221,7376,268435461,536870917]),
([pw0,pw1,pw2,pw10,pw3,pw8,pw45],[20,0,72,5,24,148,117,88,65,93,25,53,57,8,9,17,29,37,41,121,149,153,229],[11,32777,2057,65545,262153,2057,3,16387,3,3,3,2,1380,4325764,4884,101,532609,4113,1124,1049204,2097808]),
([pw127,pw0,pw1,pw2,pw3,pw8,pw45],[32,88,20,72,24,5,25,37,57,17,12,61,193,233,3],[551,2054,1,74,134,17427,549,551,45,39,309,8199,77,135,277,74,138,4115,74,345,403]),
([pw0,pw1,pw2,pw3,pw12,pw8,pw45],[20,32,0,72,5,21,24,57,17,69,73,237,8,88,9,13,29,37,41,53,85,89,109,241],[2564,275,65555,275,262163,524307,5,5,16389,5,2564,32808,41,1048616,2097194,4,8389640,1226,143361,195,4194498]),
([pw0,pw1,pw2,pw3,pw8,pw22,pw45],[88,32,20,0,21,5,24,57,77,81,245,4,72,9,13,17,25,29,53,85,89,101,157,249],[1288,4194355,131110,39,32775,262182,13,12,13,8201,1288,16401,524305,21,1048595,8389121,71681,2097346,8,707,195]),
([pw0,pw1,pw2,pw3,pw8,pw45,pw47],[32,0,5,49,24,61,3,152,156,17,25,117,121,1,9,13,29,37,41,53,85,93,221,225,237,245],[7,517,65541,262149,524293,517,8226,16777250,33554466,11,16387,36032,1184064,2097161,17,7616,4194313,17,8388617,17,2]),
([pw0,pw1,pw2,pw3,pw14,pw8,pw45],[72,164,88,4,160,1,13,3,25,45,32,168,5,9,37,49,8,53,57,65,81,89,105,141],[12464,8388677,265,5123,16898,428160,524401,57,51,1049142,43184,77,9,16455,2097221,4,269,265,65667,1027,4194818]),
([pw128,pw0,pw1,pw2,pw3,pw8,pw45],[88,4,121,172,61,3,32,33,93,141,176,9,37,24,96,5,13,17,21,25,45,53,57,65,81,89,105,117,241,253],[131169,8273,262145,524291,4101,16705,34872,66049,134217858,1048581,6292768,8388633,268435594,16777221,3384,515,4101,33554945,7,536871042,67108869]),
([pw0,pw1,pw2,pw3,pw8,pw23,pw45],[88,72,180,1,8,184,25,164,145,3,32,188,5,9,37,49,4,33,53,57,73,85,97,229,257],[12812,2097409,131170,16401,5249,821760,8388877,1048686,29,141,43532,193,273,17,16777473,99,66083,4194402,3,16401,1153]),
([pw129,pw0,pw1,pw2,pw3,pw8,pw45],[88,164,25,61,3,32,192,93,145,196,9,24,96,5,17,21,33,37,53,57,73,85,97,121,209,229,257],[16433,2089,32769,7,131073,4257,9304,2097409,65542,3,787088,33554505,1048582,3,1752,7,25166081,67109121,7,4194310,3]),
([pw0,pw1,pw2,pw3,pw8,pw45,pw48],[96,32,164,200,5,1,24,93,9,117,121,12,17,25,37,89,257,72,88,29,41,53,61,69,77,193],[314,4115,524307,1048595,2097171,4115,4194408,8388712,16777320,427,329,107012,115716,33554567,2,26116,2179,131589,2179,263173,5]),
([pw130,pw0,pw1,pw2,pw3,pw8,pw45],[88,96,164,24,17,25,37,57,89,0,9,49,93,121,133,161,217,261,265,3],[19,524809,9,37,67,4099,1050,19,32774,19,65682,131337,16428,5,2178,37,8513,262147,37,38,7]),
([pw0,pw1,pw2,pw3,pw8,pw24,pw45],[88,164,204,1,21,13,33,3,4,208,9,49,5,25,53,57,65,85,89,117,121,241,253],[5260,49,524354,3,3,51840,65565,2097230,15,15,3724,49,131089,49,262161,1048835,8195,4194370,257,3,3]),
([pw0,pw1,pw2,pw3,pw8,pw45,pw49],[164,24,96,212,1,17,13,12,9,37,21,29,97,121,221,253,72,88,5,41,53,61,69,77,85],[282,262245,2085,524325,1048614,2084,2097178,4194330,8388634,16670,282,37953,16785985,199,66565,45569,135,2,16519,131589,1]),
([pw0,pw1,pw2,pw3,pw8,pw45,pw50],[96,88,216,5,65,24,1,69,12,164,21,41,225,72,17,25,29,53,85,105,269,273],[1048653,16393,65545,2057,131081,2057,1110,228,102,4229,165,1042,262162,19,19,2621442,4353,41473,259,35,513])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p15_D7 : List StD := [
([pw51,pw0,pw1,pw2,pw3,pw8],[96,220,9,93,113,3,228,232,25,117,121,277,224,5,13,29,37,41,57,69,77,85,101,109,281],[4098,2054,262153,4194313,8388617,2054,8209,32785,131089,16777222,524294,1048582,17248,2163872,2016]),
([pw0,pw1,pw18,pw2,pw3,pw14,pw8,pw45],[57,5,9,81,25,65,164,13,49,69,93,113,121,3,40,72,168,1,17,21,29,37,73,117,137,153,173,181,201,205,285,289],[1073741830,262144,2050,1048578,2050,402653186,259,131072,164,516,516,83886084,261,160,4194320,32832,2097224,73729,536870960,524288,4136,1025,8388608,4120,2147483665,24584,1025,33554441]),
([pw128,pw0,pw1,pw18,pw2,pw3,pw8,pw45],[93,121,5,9,57,24,88,37,65,117,13,113,0,32,176,1,17,21,25,33,81,133,137,149,153,161,181,285,293,297,301,3],[2052,4136,8288,131072,262144,130,49,134217740,65536,2052,301989892,67108870,21,32768,1288,538968072,4194314,25,1344,524800,1048642,2147500033,1073742592,130,17,130,8389121,16777219]),
([pw0,pw1,pw18,pw2,pw3,pw8,pw23,pw45],[57,5,9,25,229,37,49,77,85,93,113,117,3,24,32,36,88,188,1,17,21,41,73,81,121,133,149,161,177,285,293,297,305],[536870918,524288,1026,1207959554,2097154,1026,67,262144,276,2181038084,132,132,69,272,4194312,8388640,90112,135169,2072,268435504,1048576,513,2056,36872,67108873,16777216,4294967329,513]),
([pw129,pw0,pw1,pw18,pw2,pw3,pw8,pw45],[93,117,5,9,57,24,88,25,121,229,85,113,0,32,196,1,17,21,37,45,73,133,137,149,153,161,173,181,201,209,285,3],[2052,4136,8288,131072,130,262144,49,1073741836,65536,2052,33554438,402653188,21,32768,1544,2097162,71303176,25,1600,1048578,524608,2147500033,130,536871680,17,130,8388611,16777473]),
([pw0,pw1,pw18,pw2,pw3,pw8,pw24,pw45],[21,57,5,9,65,121,36,29,49,69,101,24,32,88,208,1,13,17,25,33,41,45,77,85,117,193,285,309,313,3],[67108876,131072,134217733,132,1048580,132,262,32768,25,520,4194312,520,266,65537,17301504,2097184,14336,536887298,17,8388609,17,33554435,96,262144,1026,64,268435490,1026]),
([pw0,pw1,pw2,pw131,pw3,pw8,pw45],[32,1,17,57,5,25,37,49,117,121,21,61,4,8,72,88,29,41,93,101,109,141,145,237,245],[23,21,21,65541,131077,141,2051,2051,8388611,16777219,139,1,2098464,4195904,262153,20768,41536,137,864,524297,1048585]),
([pw112,pw0,pw1,pw2,pw3,pw14,pw8,pw45],[45,49,13,25,1,32,37,5,57,72,164,29,93,141,4,56,9,17,21,61,117,153,189,205,269,289,317,321,3],[131072,65536,8196,16904,1568,1089,258,16777360,8196,2184,2208,65,258,4194324,67108888,524336,134217745,258,8388620,262144,69,4102,1048576,73,33554442,268468225,4130,2097155]),
([pw128,pw112,pw0,pw1,pw2,pw3,pw8,pw45],[93,121,61,113,57,117,32,72,37,1,5,33,45,141,9,13,17,21,25,149,153,269,301,321,325,3],[33554624,1096,580,131072,262144,258,81,65536,16384,41088,2208,4098,17,2097164,1032,2088,4106,25,516,16777252,8388614,21,4202528,258,17,258,524321,1048579]),
([pw112,pw0,pw1,pw2,pw3,pw8,pw23,pw45],[25,49,85,1,37,32,33,5,57,88,41,93,145,8,52,164,9,17,21,61,121,149,177,269,305,317,321,329,3],[131072,65536,4100,65,8720,33312,258,8388744,4100,65,1168,1184,258,134217740,33554441,67108888,524328,258,69,4194324,262144,2054,65,268451841,2097155,1048576,16777234,2082]),
([pw129,pw112,pw0,pw1,pw2,pw3,pw8,pw45],[93,117,61,113,45,57,32,164,25,1,5,33,121,145,9,17,21,37,85,149,153,209,269,317,333,3],[33554624,1096,580,65536,258,131072,97,32768,16384,270464,2178,4240,33,4194316,1032,2058,4120,41,516,8388614,16777236,37,258,2105360,33,258,524291,1048593]),
([pw112,pw0,pw1,pw2,pw3,pw8,pw24,pw45],[13,49,1,117,32,21,121,57,56,5,33,45,101,72,164,9,17,29,37,85,189,193,237,269,313,325,333],[65536,32768,33,1032,2112,24592,130,8389124,33,1032,2112,131600,130,1048581,33554444,67108932,4194324,130,33,524289,33,2097155,264,256,4106,262144,16777282,4114]),
([pw0,pw132,pw2,pw3,pw8,pw45],[32,164,9,53,25,61,85,285,13,29,37,41,69,77,121,149,153,193,269,301],[262157,137,521,2057,137,37,4101,8197,37,524370,322,131075,17426,32771,65539]),
([pw0,pw1,pw2,pw133,pw8,pw45],[32,164,236,1,9,85,205,5,25,37,57,121,125,133,137,149,153,161,181,189,193,217],[29,4099,131075,262147,2098305,524303,8207,16399,29,98,98,1048579,2818,32771,65539]),
([pw0,pw1,pw2,pw3,pw134,pw45],[32,164,240,1,9,25,177,5,13,37,57,121,125,133,137,149,153,161,181,189,193,217,301],[29,4099,131075,262147,2098305,524303,8207,16399,29,4194402,322,1048579,2594,32771,65539]),
([pw0,pw1,pw2,pw3,pw8,pw135],[32,164,244,1,213,5,9,25,85,13,29,37,41,61,69,77,121,149,153,193,301],[77,49,1041,4113,49,8205,16397,32781,77,1048962,770,524291,67714,131075,262147]),
([pw0,pw1,pw2,pw19,pw3,pw8,pw45],[164,32,1,17,33,9,45,21,49,57,25,61,93,113,117,121,133,137,149,153,177,205],[8236,3,1,27,75,778,2055,38,65543,131079,38,2,2097297,1048769,4099,16401,32833,770,1041,262147,524291]),
([pw0,pw1,pw2,pw3,pw136,pw45],[32,72,248,1,9,21,57,25,181,13,29,49,117,189,193,293,301,337],[29,35,32771,1281,131393,8207,15,29,29,65698,546,16387,4226,67,2113]),
([pw0,pw1,pw2,pw137,pw8,pw45],[32,72,252,1,9,21,41,57,85,5,25,49,77,109,117,161,189,193,341],[29,35,515,32833,262337,65551,29,4109,29,290,290,131075,17410,2051,8321]),
([pw138,pw0,pw2,pw3,pw8,pw45],[32,9,269,57,3,256,260,25,61,117,121,13,17,37,53,69,77,85,101,109,281,345,349,353],[4103,259,32771,65539,259,2097157,4194309,8388613,16397,2736,140368,1048585,1776,262153,524297]),
([pw0,pw1,pw2,pw3,pw14,pw8,pw45,pw46],[9,45,53,141,37,57,1,13,25,69,101,165,3,32,72,136,160,164,5,21,49,89,97,117,137,153,189,205,213],[69,140,2052,2052,22,268435492,262144,67108873,513,513,16777219,65,69633,134217992,524288,26,2097160,136,8388608,18,1056,4194560,36866,1056,155648,33554466,18,1048576]),
([pw128,pw0,pw1,pw2,pw3,pw8,pw45,pw46],[9,121,53,33,57,61,13,37,32,96,45,89,117,129,172,5,21,25,49,133,137,149,153,213,301,3],[8196,33,65536,131072,130,784,768,37,8196,4108,1030,8388628,32768,33,524297,1048579,33,33570817,16777288,130,2128,2112,130,2097176,4104,4194322,1026,262144]),
([pw0,pw1,pw2,pw3,pw8,pw23,pw45,pw46],[9,33,53,145,25,57,1,37,77,85,109,185,3,32,96,132,180,5,21,49,105,121,133,149,177,213,257,329],[69,524,22,2052,2052,33554468,131072,134217737,4194307,257,257,65,69633,26,16777352,262144,67108872,520,18,36866,8388642,18,2097152,1056,1048704,1056,24576,524288]),
([pw129,pw0,pw1,pw2,pw3,pw8,pw45,pw46],[9,117,53,45,57,61,25,85,32,96,33,121,129,257,192,5,21,37,49,133,137,149,153,209,213,3],[4100,33,65536,66,131072,784,768,37,4100,1030,2060,16777236,32768,33,524291,1048585,33,33570817,66,8388744,8336,8320,66,2097170,1026,4194328,2056,262144]),
([pw0,pw1,pw2,pw3,pw8,pw24,pw45,pw46],[9,21,53,13,45,57,33,132,1,69,101,117,121,32,96,204,5,25,49,77,85,89,109,165,189,213,3],[261,14,2116,4116,8388612,33554468,65536,16777219,513,524289,513,257,67141633,10,1048578,10,2097154,10,144,131072,1120,2112,128,4194352,4112,1056,24576,262144]),
([pw0,pw1,pw2,pw139,pw3,pw8,pw45],[96,32,1,17,9,21,25,37,53,117,121,4,72,88,164,61,69,77,113,141,145,165,185],[262172,265,265,2097161,4194313,265,32806,22,65542,131078,22,1,524896,1049760,3,6720,25728,3,1728,3,3]),
([pw126,pw0,pw1,pw2,pw3,pw14,pw8,pw45],[1,45,13,25,49,37,9,165,72,164,53,69,93,141,4,144,5,21,57,117,137,189,205,217,289,357,3],[65536,65,8196,16648,768,546,262144,65,8196,1160,1152,34,8388752,2097157,2049,2049,1048579,65,4194316,131072,38,4116,524288,42,16777240,67141634,4112,33554450]),
([pw126,pw128,pw0,pw1,pw2,pw3,pw8,pw45],[1,45,33,37,49,141,164,96,9,13,61,93,117,129,5,21,25,53,57,133,137,217,301,357,361,3],[33554624,16384,257,608,4164,74,262144,139392,1025,32768,65536,10,2192,257,544,4100,10,2105360,1025,524293,1048579,257,4194340,42,2096,14,16777236,8388626]),
([pw126,pw0,pw1,pw2,pw3,pw8,pw23,pw45],[1,25,85,49,33,37,9,185,88,164,53,77,93,145,140,5,21,57,121,133,177,217,305,329,361,3],[32768,65,8196,18,800,768,131072,65,8196,18,1184,1152,2097288,8388613,524291,2049,2049,65,22,1048612,65536,4108,18,33570818,16777226,262144,4194344,4104]),
([pw126,pw129,pw0,pw1,pw2,pw3,pw8,pw45],[1,33,25,45,49,145,164,96,9,61,85,93,121,129,5,21,37,53,57,133,137,209,217,357,361,3],[33554624,16384,257,1120,70,4168,262144,139392,513,32768,6,65536,2192,257,1056,6,4104,4202512,513,524291,1048585,257,38,2097192,2096,6,16777234,8388632]),
([pw126,pw0,pw1,pw2,pw3,pw8,pw24,pw45],[1,13,49,21,121,9,117,140,33,45,53,69,221,88,164,5,25,57,77,85,165,189,193,217,313],[32768,33,10,320,528,24576,131072,33,10,320,528,1049600,8389636,2097155,2049,262145,2049,33,10,524290,10,4194310,144,65536,4164,128,16777236,4100]),
([pw0,pw1,pw2,pw3,pw8,pw140],[164,96,200,65,1,9,17,121,229,5,25,37,73,133,137,161,181],[52,67,32771,65539,578,13,8197,16389,52,265,265,15,3201,4099,131]),
([pw0,pw1,pw2,pw3,pw14,pw8,pw45,pw47],[17,81,13,25,49,5,160,1,37,65,73,93,121,72,96,156,164,9,21,29,53,61,117,181,201,205,221,357,3],[33,33,524289,33,25165825,1048577,33,516,1032,2097280,386,80,131072,33554444,262144,4102,2068,516,4194304,4106,67108888,1032,268468226,2064,90112,134217746,258,64]),
([pw128,pw0,pw1,pw2,pw3,pw8,pw45,pw47],[5,121,49,1,17,241,164,37,172,13,61,81,93,117,32,96,9,21,25,53,65,161,181,293,301,357,361],[17,1032,131072,262144,130,4100,49216,17,17,10485761,4194307,524289,17,1032,8232,2058,260,65536,16777760,130,4100,1049152,130,67108900,8288,33554438,2050,256]),
([pw0,pw1,pw2,pw3,pw8,pw23,pw45,pw47],[17,25,49,85,5,37,180,73,81,93,117,229,32,96,152,164,1,9,21,41,53,61,121,161,177,225,293,361,3],[17,17,75497473,524289,17,1048577,17,2056,130,288,2162688,68,131072,1034,16777256,262144,524,2056,1026,268451842,134217734,130,4194304,33554468,288,516,45056,64]),
([pw129,pw0,pw1,pw2,pw3,pw8,pw45,pw47],[5,117,49,1,17,249,25,192,61,73,85,93,121,32,96,9,21,37,53,161,181,201,209,229,357,361],[17,264,65536,66,131072,2052,24576,17,17,524291,3145729,262145,17,264,522,4136,132,32768,66,4195360,2052,8389632,66,33554438,514,16777252,4128,128]),
([pw0,pw1,pw2,pw3,pw8,pw24,pw45,pw47],[17,21,49,65,121,5,117,152,204,29,221,241,249,32,96,1,9,25,41,53,85,193,225,237],[33,33,513,262145,513,524289,33,10,2112,4112,8421376,260,65536,10,1048578,10,2097158,10,144,131072,1092,2112,128,4194324,4112,1028,24576,256]),
([pw68,pw0,pw1,pw2,pw3,pw45],[164,45,264,141,365,37,3,268,1,9,25,49,5,13,53,57,65,73,81,89,97,105],[35,262147,35,35,2097155,4932,8201,1041,51392,65549,131093,3012,1049,524297,1048593]),
([pw0,pw141,pw1,pw2,pw3,pw8,pw45],[164,21,45,33,1,9,13,37,49,57,24,17,117,0,96,65,81,89,105,113,121,129,241,253],[1,526384,67,4105,133,2099968,9264,67,4105,1048581,18176,32771,4194313,65541,816,67,135,131075,141,8388617,262149]),
([pw71,pw0,pw1,pw2,pw8,pw45],[164,33,272,365,369,25,3,276,1,9,37,49,5,53,57,73,81,97,105,301,373,377],[35,32771,35,35,131075,4932,524305,1033,26816,1048597,65549,3012,1049,2097169,262153]),
([pw0,pw142,pw1,pw2,pw3,pw8,pw45],[164,21,33,45,1,9,25,49,57,85,24,17,121,0,96,73,97,113,117,129,229,249,257,273],[1,133168,515,69,4105,526720,9264,515,262149,4105,17792,1048579,32773,2097161,432,71,515,4194307,69,65541,8388617]),
([pw0,pw143,pw2,pw3,pw8,pw45],[96,164,5,25,189,37,117,53,121,17,29,41,49,57,89],[133,517,1029,2053,133,16402,74,290,12289,90,306,19,74,11,35])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p15_D6 : List StD := [
([pw51,pw0,pw1,pw2,pw3,pw14,pw8],[81,217,9,57,141,73,5,13,25,29,37,121,232,21,65,69,93,117,181,205,277,3],[66,1048588,152,296,65544,1033,66,146,514,514,262147,16404,292,32772,1029,524336,8192,2065,131072,2081,2101249]),
([pw51,pw128,pw0,pw1,pw2,pw3,pw8],[57,81,33,5,9,93,121,281,37,113,117,13,21,25,133,181,301],[33,33,33,33,1029,259,520,144,4096,8192,66,152,520,1028,32778,144,16404,258,67588,66,70]),
([pw51,pw0,pw1,pw2,pw3,pw8,pw23],[73,217,9,57,145,81,5,25,37,41,85,117,228,21,77,93,121,161,177,229,277,3],[66,1048588,1048,137,296,32776,66,1042,131075,514,514,524308,133,292,16388,2065,262192,8192,2049,2101249,65536]),
([pw51,pw129,pw0,pw1,pw2,pw3,pw8],[57,73,45,5,9,93,117,281,25,113,121,21,37,85,137,161,209],[33,33,33,33,259,1029,520,144,2048,66,4096,152,520,32778,1028,144,258,16404,66,73732,70]),
([pw51,pw0,pw1,pw2,pw3,pw8,pw24],[21,217,9,57,13,45,228,5,33,69,117,121,25,29,65,77,85,101,277],[130,262156,25,1288,2088,131080,130,19,1282,2082,8194,16389,516,32772,516,17,65537,17,96,4096,64]),
([pw68,pw0,pw1,pw18,pw2,pw3,pw45],[93,5,9,209,25,37,57,65,69,113,381,268,1,17,21,29,73,81,285,385,3],[514,260,131104,16424,1072,97,262150,8192,514,32770,67,4096,140,260,69,136,65552,1050625,1048,73,524305]),
([pw71,pw0,pw1,pw18,pw2,pw8,pw45],[93,5,9,73,301,37,57,25,113,373,381,276,1,17,21,41,77,81,285,385,3],[258,140,136,16408,1064,73,262150,8192,258,32770,67,4096,532,65540,69,528,131104,1050625,1072,81,524321]),
([pw68,pw112,pw0,pw1,pw2,pw3,pw45],[37,93,25,57,13,45,1,365,141,5,9,17,189,269,317,321,385,389],[33,33,163841,33,33,11,2048,1024,272,132,10,8768,272,132,10,4176,16452,10,148,10,65542]),
([pw144,pw0,pw1,pw2,pw3,pw8,pw45],[5,49,121,1,117,13,17,37,57,21,33,61,9,25,93,149,153,181,321,325],[65,6152,544,9232,132,258,65,65,1041,131077,259,2056,524312,262156,266,544,164,16418,148,32786,65542]),
([pw71,pw112,pw0,pw1,pw2,pw8,pw45],[25,93,37,57,33,301,1,365,369,5,9,17,269,317,321,385,393,397],[17,17,73729,17,17,11,2048,1024,288,132,10,4672,288,132,10,131168,16452,10,164,10,32774]),
([pw145,pw0,pw1,pw2,pw3,pw8,pw45],[5,49,117,1,85,121,17,25,57,21,45,61,9,37,93,149,153,161,317,333],[65,6152,528,132,9248,258,65,65,131077,1057,259,2056,262156,524328,266,148,528,16402,132,32774,65570]),
([pw138,pw0,pw2,pw3,pw14,pw8,pw45],[9,57,269,141,37,13,25,69,121,277,281,349,260,17,21,101,117,137,153,173,205,401,405,3],[8197,41,129,129,655361,515,44,2052,2052,6291460,518,1048648,16384,280,1034,65536,336,32770,8392720,1026,262162]),
([pw128,pw138,pw0,pw2,pw3,pw8,pw45],[9,121,57,269,61,37,281,117,345,13,21,25,133,149,153,173,297,301,401,409,413],[17,264,1024,2048,34,68,17,17,69633,32771,17,264,1572872,262154,76,131712,34,68,34,8324,16390]),
([pw138,pw0,pw2,pw3,pw8,pw23,pw45],[9,57,269,145,25,77,85,117,277,281,353,256,17,21,37,109,121,133,149,177,297,409,413,3],[4101,73,1179649,33,33,259,76,6291460,1028,1028,262,152,540680,8192,522,144,8390672,262162,65536,32770,514]),
([pw129,pw138,pw0,pw2,pw3,pw8,pw45],[9,117,57,269,61,25,281,121,345,21,37,85,137,149,153,173,209,297,401,405,409],[17,264,512,34,1024,68,17,17,131075,36865,17,264,1048586,786440,76,34,67712,68,34,8198,16516]),
([pw138,pw0,pw2,pw3,pw8,pw24,pw45],[9,21,57,269,13,256,69,101,277,349,17,25,77,85,109,121,353,417],[1033,19,65,4097,65,261,26,520,65544,520,268,18,8194,18,131078,32800,2048,132,32,16388,132]),
([pw68,pw0,pw1,pw2,pw3,pw45,pw46],[37,69,141,45,53,101,25,365,1,9,13,57,264,5,49,89,189,213,3],[9,515,9,9,2081,9,274,1044,208,131120,8192,65542,514,258,266242,196,32804,1028,2080,192,16384]),
([pw71,pw0,pw1,pw2,pw8,pw45,pw46],[9,25,369,33,53,365,37,1,57,301,272,5,49,77,97,109,213,377,393,397,3],[10,262147,10,10,16386,10,145,532,112,65808,2048,524293,8193,129,1049601,100,131076,516,33056,96,4096]),
([pw126,pw68,pw0,pw1,pw2,pw3,pw45],[1,37,13,25,45,93,9,365,49,69,141,5,53,57,189,217,385],[18,2048,65,1028,136,8192,18,515,18,18,290,65,1028,136,36896,16389,513,65,140,292,65576]),
([pw146,pw0,pw1,pw2,pw3,pw8,pw45],[1,53,121,13,117,49,9,17,37,21,33,93,25,45,57,133,137,189,357,361],[130,65,520,5136,260,18464,67,130,1042,8198,130,131081,32785,65541,65,520,268,2088,276,524336,262180]),
([pw126,pw71,pw0,pw1,pw2,pw8,pw45],[1,25,301,33,37,93,9,365,49,369,5,53,57,77,217,385,393,397],[10,1024,65,516,144,4096,10,65539,10,10,290,65,516,144,18464,131077,8193,65,148,292,32816]),
([pw147,pw0,pw1,pw2,pw3,pw8,pw45],[1,53,117,85,49,121,9,17,25,21,45,93,33,37,57,133,137,329,357,361],[130,65,520,260,9248,18448,67,130,4102,1058,130,131081,32773,65569,65,268,520,2072,260,524308,262192]),
([pw68,pw0,pw1,pw2,pw3,pw45,pw47],[5,25,37,209,17,93,264,49,65,73,81,381,9,21,29,53,221],[17,1028,8204,2054,164,1028,17,17,16385,32769,17,264,514,96,4096,2058,168,264,65570,514,64]),
([pw71,pw0,pw1,pw2,pw8,pw45,pw47],[5,25,37,301,17,93,272,49,73,81,373,381,9,21,41,53,225],[17,258,8202,2054,162,258,17,17,16385,32769,17,1032,516,96,4096,2060,168,1032,65572,516,64])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p15_D5 : List StD := [
([pw51,pw68,pw0,pw1,pw2,pw3],[37,141,217,9,57,73,5,13,25,81,209,29,65,113,277,381],[513,68,16408,146,304,8197,513,1027,32801,68,134,2052,4106,296,1026]),
([pw51,pw71,pw0,pw1,pw2,pw8],[25,217,369,81,9,57,5,37,73,301,381,21,41,113,277,373],[257,66,16432,548,168,8195,257,2053,1033,66,518,4098,32788,152,1036]),
([pw68,pw138,pw0,pw2,pw3,pw45],[9,269,281,57,209,13,25,37,69,345,17,101,141,349,381],[257,514,48,16576,140,1027,4113,257,13,514,8194,14,48,28,2116]),
([pw71,pw138,pw0,pw2,pw8,pw45],[9,269,281,57,301,25,37,77,345,381,17,21,109,353,369],[129,258,2096,608,44,1027,16401,129,13,258,8194,14,592,28,4164])]
def p15_D4 : List StD := []
theorem p15_I4 : LevelN true p15_T 4 p15_D4 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p15_C5x0 : levelOK true p15_T p15_t 4 (p15_D4.map Prod.fst) ((p15_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p15_I5 : LevelN true p15_T 5 p15_D5 := levelStep p15_B p15_W p15_I4 (chunks 32 p15_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p15_C5x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p15_C6x0 : levelOK true p15_T p15_t 5 (p15_D5.map Prod.fst) ((p15_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p15_I6 : LevelN true p15_T 6 p15_D6 := levelStep p15_B p15_W p15_I5 (chunks 32 p15_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p15_C6x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p15_C7x0 : levelOK true p15_T p15_t 6 (p15_D6.map Prod.fst) ((p15_D7.drop (0*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p15_C7x1 : levelOK true p15_T p15_t 6 (p15_D6.map Prod.fst) ((p15_D7.drop (1*32)).take 32) = true := by decide +kernel
theorem p15_I7 : LevelN true p15_T 7 p15_D7 := levelStep p15_B p15_W p15_I6 (chunks 32 p15_D7 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p15_C7x0
  · exact p15_C7x1
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p15_C8x0 : levelOK true p15_T p15_t 7 (p15_D7.map Prod.fst) ((p15_D8.drop (0*32)).take 32) = true := by decide +kernel
theorem p15_I8 : LevelN true p15_T 8 p15_D8 := levelStep p15_B p15_W p15_I7 (chunks 32 p15_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p15_C8x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p15_C9x0 : levelOK true p15_T p15_t 8 (p15_D8.map Prod.fst) ((p15_D9.drop (0*32)).take 32) = true := by decide +kernel
theorem p15_I9 : LevelN true p15_T 9 p15_D9 := levelStep p15_B p15_W p15_I8 (chunks 32 p15_D9 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p15_C9x0
  ))
theorem p15_L : LowN true p15_R p15_T 10 := lowSearch p15_B p15_I9 (by decide +kernel)
def p16_T : Nat := 0xfffffffefffefefefffffffefffefefefffffffefffefefefffffffefffefefe
def p16_R : List Nat := [0, 1, 2, 3, 4, 5]
def p16_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,0,4),(3,16,24),(4,8,24),(5,8,40)]
theorem p16_B : baseOK p16_T p16_R p16_E = true := by decide +kernel
def p16_Z : List SliceD := [(pw4,6,[1, 2, 3, 4, 5])]
theorem p16_Y : ∀ s ∈ p16_Z, SliceN true p16_R p16_T s := by
  unfold p16_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p16_B p11_B p11_L (by decide +kernel),by simp⟩
def p16_C : List (Nat × List Nat) := [(0,[])]
def p16_t : Tabs := (p16_C.map (mkCut true p16_Z),[(1,0),(2,0)],[],[[]])
theorem p16_W : TabsP true p16_R p16_T p16_t := ⟨cutsGood p16_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p16_D6 : List StD := [
([pw0,pw1,pw2,pw3,pw8,pw45],[0,1,5],[7,3,3,3,3,5,5,5,5,1,1,1,1,1,1])]
def p16_D5 : List StD := []
theorem p16_I5 : LevelN true p16_T 5 p16_D5 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p16_C6x0 : levelOK true p16_T p16_t 5 (p16_D5.map Prod.fst) ((p16_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p16_I6 : LevelN true p16_T 6 p16_D6 := levelStep p16_B p16_W p16_I5 (chunks 32 p16_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p16_C6x0
  ))
theorem p16_L : LowN true p16_R p16_T 7 := lowSearch p16_B p16_I6 (by decide +kernel)
def p17_T : Nat := 0xfffffffcffffffecfffffff8ffe8e8e8fffffffcffffffecfffffff8ffe8e8e8
def p17_R : List Nat := [0, 1, 2, 3, 4, 5, 6]
def p17_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,16,24),(4,8,24),(5,4,36),(6,2,66)]
theorem p17_B : baseOK p17_T p17_R p17_E = true := by decide +kernel
def p17_Z : List SliceD := [(pw4,10,[5, 1, 6, 4, 3, 2]),(pw5,9,[1, 2, 4, 5, 6, 0]),(pw9,9,[1, 2, 3, 5, 6, 0]),(pw29,10,[1, 0, 6, 3, 4, 2]),(pw148,10,[2, 1, 5, 3, 4, 0]),(pw149,7,[6, 3, 4, 5, 1]),(pw150,7,[5, 3, 4, 6, 2]),(pw1,7,[0, 2, 6, 4, 5, 3]),(pw2,7,[0, 1, 5, 4, 3, 6]),(pw151,5,[3, 4, 5, 6]),(pw11,6,[0, 6, 4, 5, 3]),(pw119,6,[5, 6, 2, 0, 1]),(pw127,6,[0, 5, 4, 3, 6]),(pw152,6,[5, 6, 2, 0, 1]),(pw40,6,[1, 2, 0, 5, 6]),(pw153,7,[1, 6, 3, 4, 0]),(pw154,7,[2, 5, 3, 4, 0]),(pw113,6,[2, 6, 4, 5, 3]),(pw126,6,[1, 2, 3, 4, 6]),(pw155,5,[0, 3, 4, 6]),(pw156,5,[0, 3, 4, 5]),(pw44,7,[6, 1, 2, 0, 4]),(pw123,6,[1, 5, 4, 3, 6])]
theorem p17_Y : ∀ s ∈ p17_Z, SliceN true p17_R p17_T s := by
  unfold p17_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p17_B p9_B p9_L (by decide +kernel),mkSlice (w:=0) p17_B p13_B p13_L (by decide +kernel),mkSlice (w:=0) p17_B p13_B p13_L (by decide +kernel),mkSlice (w:=0) p17_B p15_B p15_L (by decide +kernel),mkSlice (w:=0) p17_B p15_B p15_L (by decide +kernel),mkSlice (w:=0) p17_B p6_B p6_L (by decide +kernel),mkSlice (w:=0) p17_B p6_B p6_L (by decide +kernel),mkSlice (w:=2) p17_B p16_B p16_L (by decide +kernel),mkSlice (w:=4) p17_B p16_B p16_L (by decide +kernel),mkSlice (w:=0) p17_B p8_B p8_L (by decide +kernel),mkSlice (w:=2) p17_B p11_B p11_L (by decide +kernel),mkSlice (w:=8) p17_B p11_B p11_L (by decide +kernel),mkSlice (w:=4) p17_B p11_B p11_L (by decide +kernel),mkSlice (w:=16) p17_B p11_B p11_L (by decide +kernel),mkSlice (w:=0) p17_B p10_B p10_L (by decide +kernel),mkSlice (w:=0) p17_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p17_B p5_B p5_L (by decide +kernel),mkSlice (w:=2) p17_B p11_B p11_L (by decide +kernel),mkSlice (w:=1) p17_B p11_B p11_L (by decide +kernel),mkSlice (w:=4) p17_B p3_B p3_L (by decide +kernel),mkSlice (w:=2) p17_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p17_B p5_B p5_L (by decide +kernel),mkSlice (w:=4) p17_B p11_B p11_L (by decide +kernel),by simp⟩
def p17_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(0,[644]),(5,[]),(0,[646]),(3,[640]),(4,[128]),(6,[]),(2,[128]),(1,[128]),(0,[645]),(7,[]),(3,[641]),(8,[]),(4,[129]),(1,[129]),(9,[]),(2,[129]),(3,[642]),(4,[131]),(2,[130]),(1,[130]),(0,[647]),(3,[643]),(4,[130]),(2,[131]),(1,[131]),(0,[517]),(3,[385]),(4,[389]),(10,[]),(2,[257]),(11,[]),(0,[518]),(3,[386]),(4,[390]),(2,[258]),(12,[]),(0,[389]),(3,[513]),(4,[517]),(1,[257]),(13,[]),(0,[390]),(3,[514]),(4,[518]),(1,[258]),(0,[657]),(2,[261]),(3,[653]),(4,[385]),(0,[659]),(3,[655]),(4,[386]),(2,[262]),(0,[653]),(1,[261]),(3,[657]),(4,[513]),(0,[655]),(3,[659]),(4,[514]),(1,[262]),(0,[525]),(14,[]),(3,[525]),(4,[525]),(1,[128,665]),(2,[128,665]),(3,[640,153]),(4,[128,665]),(0,[644,537]),(3,[640,409]),(4,[128,409]),(2,[128,281]),(0,[644,409]),(3,[640,537]),(4,[128,537]),(0,[644,25]),(2,[128,409]),(1,[128,409]),(15,[]),(4,[128,281]),(0,[644,281]),(2,[128,537]),(1,[128,537]),(3,[640,281]),(16,[]),(5,[261]),(0,[525,646]),(3,[525,640]),(4,[525,128]),(6,[261]),(1,[129,791]),(3,[641,775]),(4,[129,791]),(2,[129,791]),(1,[129,666]),(17,[]),(2,[129,666]),(3,[641,154]),(4,[129,666]),(0,[517,665]),(3,[385,665]),(4,[129,409]),(0,[645,538]),(5,[519]),(6,[519]),(2,[129,282]),(3,[641,410]),(4,[129,410]),(0,[389,665]),(5,[521]),(0,[645,781]),(0,[653,154]),(3,[513,665]),(4,[129,537]),(0,[389,666]),(0,[645,410]),(3,[641,538]),(4,[129,538]),(0,[645,525]),(3,[641,525]),(4,[129,525]),(0,[646,537]),(3,[642,409]),(4,[131,409]),(2,[130,281]),(0,[646,409]),(0,[391]),(3,[642,537]),(4,[131,537]),(0,[525,644]),(0,[525,645]),(3,[525,642]),(4,[525,131]),(0,[647,537]),(4,[130,409]),(0,[517,667]),(2,[131,281]),(3,[643,409]),(0,[647,409]),(4,[130,537]),(3,[643,537]),(0,[525,647]),(3,[525,643]),(4,[525,130]),(0,[517,389]),(0,[389,518]),(4,[389,517]),(3,[513,385]),(0,[517,390]),(3,[385,514]),(4,[389,518]),(0,[517,657]),(3,[653,385]),(4,[389,385]),(0,[517,666]),(0,[658]),(0,[518,666]),(2,[257,154]),(3,[385,666]),(4,[389,26]),(0,[517,653]),(4,[389,513]),(3,[657,385]),(0,[389,537]),(3,[385,537]),(4,[389,537]),(0,[389,538]),(0,[517,410]),(3,[385,538]),(4,[389,538]),(0,[518,665]),(3,[386,665]),(4,[390,25]),(0,[518,409]),(3,[386,537]),(4,[390,537]),(1,[259]),(3,[513,386]),(4,[517,390]),(0,[657,389]),(3,[653,513]),(4,[385,517]),(0,[389,653]),(3,[513,657]),(4,[517,513]),(3,[513,666]),(4,[517,26]),(0,[391,538]),(3,[513,410]),(4,[517,410]),(0,[390,665]),(3,[514,665]),(4,[518,25]),(0,[390,537]),(3,[514,409]),(4,[518,409]),(0,[657,154]),(0,[519]),(3,[653,26]),(4,[385,154]),(0,[657,653]),(0,[653,659]),(3,[653,657]),(4,[513,385]),(0,[657,655]),(1,[260]),(3,[653,659]),(4,[385,514]),(0,[525,665]),(3,[525,665]),(4,[385,537]),(0,[657,410]),(3,[653,538]),(4,[385,538]),(0,[659,153]),(3,[655,25]),(4,[386,153]),(0,[659,409]),(0,[654]),(3,[655,537]),(4,[386,537]),(1,[263]),(3,[657,655]),(4,[513,386]),(3,[657,26]),(4,[513,154]),(0,[653,538]),(3,[657,410]),(4,[513,410]),(0,[655,153]),(3,[659,25]),(4,[514,153]),(0,[655,537]),(3,[659,409]),(4,[514,409]),(0,[525,154]),(0,[391,537]),(0,[388]),(3,[525,26]),(4,[525,154]),(0,[525,666]),(0,[654,537]),(0,[656]),(0,[658,409]),(0,[652]),(3,[525,666]),(4,[525,26]),(3,[525,640,157]),(4,[525,128,669]),(0,[525,644,29]),(15,[393]),(4,[525,128,285]),(0,[525,644,285]),(16,[393]),(3,[525,641,158]),(4,[525,129,670]),(15,[257,534]),(18,[]),(15,[385,534]),(0,[653,152]),(0,[390,666]),(2,[257,152]),(17,[257]),(1,[261,24]),(19,[]),(20,[]),(1,[257,538]),(2,[257,538]),(21,[517,22]),(1,[257,152]),(17,[513]),(0,[657,152]),(2,[261,24]),(1,[261,410]),(2,[261,410]),(5,[261,406]),(22,[])]
def p17_t : Tabs := (p17_C.map (mkCut true p17_Z),[(3,2),(5,4),(11,10),(19,18),(35,34),(69,68),(3,1),(5,1),(6,4),(6,2),(24,16),(11,9),(26,18),(24,8),(19,17),(26,10),(42,10),(36,4),(66,2),(72,8),(13,9),(28,20),(21,17),(28,12),(76,12),(40,32),(48,16),(80,16),(66,34),(36,34),(3,33),(3,65),(5,33),(5,65),(48,32),(40,8),(14,12),(22,20),(70,68),(14,10),(22,18),(3,34),(5,68),(6,0),(24,10),(40,10),(6,10),(36,0),(50,34),(50,18),(24,0),(36,12),(24,18),(6,18),(66,18),(42,34),(5,17),(21,1),(36,20),(35,1),(66,0),(24,12),(72,12),(84,68),(84,20),(66,10),(24,20),(76,68),(35,33),(66,64),(36,32),(69,65),(72,64),(6,20),(6,34),(6,68),(3,0),(11,8),(19,16),(35,32),(67,64),(13,8),(5,0),(21,16),(37,32),(69,64),(38,2),(14,4),(70,4),(3,10),(5,9),(38,34),(3,9),(19,9),(19,1),(6,8),(14,2),(26,2),(3,17),(13,1),(11,17),(6,16),(22,2),(21,9),(13,12),(28,4),(11,1),(13,17),(3,18),(21,20),(22,4),(25,17),(25,9),(35,2),(25,16),(41,32),(73,64),(80,64),(100,68),(25,8),(49,32),(41,33),(49,33),(41,9),(73,9),(44,12),(72,0),(80,0),(98,34),(98,32),(74,10),(100,64)],[],[[]])
theorem p17_W : TabsP true p17_R p17_T p17_t := ⟨cutsGood p17_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p17_D11 : List StD := [
([pw0,pw1,pw2,pw3,pw8,pw45,pw157],[0,1,3,4,8,12,16,41,53,65,73,69,5,77,9,13,17,21,25,29,33,37,45,49,57,61,81,85,89,93,97,101,105,109,113],[4099,4099,16387,32771,65539,131075,3932164,12583052,50331924,2592,9280,201326732,805306644,2592,1073742912,2147484060,2728,9416,4294968112,8589935952,17179869280])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p17_D10 : List StD := [
([pw0,pw158,pw1,pw2,pw3,pw8,pw45,pw157],[24,20,1,32,36,3,40,44,48,5,45,77,81,137,4,8,28,9,13,17,21,25,29,37,41,53,57,69,73,89,105,109,113,117,121,125,129,133,141],[39,518,519,131078,262150,524294,1048582,65537,8388609,16417,32801,41,49,8589934657,2098240,67109952,17179869256,34359738448,4198401,536875009,68719476745,137438953489,50340256,275012124936,268437776,1073750152,2147485840,4294967320]),
([pw0,pw1,pw2,pw10,pw3,pw8,pw45,pw157],[56,52,1,24,40,60,68,33,37,65,76,97,3,64,69,72,5,41,61,73,8,80,9,13,17,21,49,53,77,101,105,109,113,117,141,145,149,153,157,161],[65542,65542,4102,4194310,8388614,16777222,33554438,8589935000,8,34359738513,68719476881,17073,137438953617,16,274877915400,549755822344,17192,534856,67277825,135533569,17179870753,268438593,539398144,16928,526400,1073742368,2147485760,4294967392]),
([pw11,pw0,pw1,pw2,pw3,pw8,pw45,pw157],[40,28,84,88,1,65,73,64,24,5,33,3,96,29,49,61,4,8,52,92,9,13,25,69,77,81,89,105,109,113,129,133,137,145,149,165,169,173],[530,4194305,262145,83969,165889,37,73,530,530,1048594,2097170,34359738374,68719476746,137438954753,8589935617,17179870209,37,73,33563008,67117440,1073741988,2147483848,4295546880,8392740,16777288,134217764,268435528,536870924]),
([pw127,pw0,pw1,pw2,pw3,pw8,pw45,pw157],[24,100,104,108,5,69,97,56,40,1,37,3,116,25,85,93,4,8,52,112,9,13,29,45,57,73,105,109,113,121,125,137,141,157,161,165,169,173],[530,262145,4194305,83969,165889,37,73,530,530,1048594,2097170,34359738374,68719476746,137438954753,8397184,16785792,536871076,1073742024,8589935617,17179870209,37,73,2148063232,4294967332,33558600,67108900,134217800,268435468]),
([pw0,pw1,pw2,pw3,pw12,pw8,pw45,pw157],[56,120,1,4,40,124,128,45,3,69,73,132,136,5,53,29,49,77,109,141,24,140,9,13,17,21,37,89,93,97,105,113,137,145,177,181,185,189],[8198,8198,4194310,8198,8388614,16777222,33554438,8589934737,152,9,17179885969,34359739057,132305,68719542536,68192513,402692352,137438956064,536872000,16,86024,524328,131144,4297085185,524833,263233,1073742368,263232,2147483744]),
([pw13,pw0,pw1,pw2,pw3,pw8,pw45,pw157],[40,4,144,148,152,1,73,193,197,156,160,5,145,3,37,85,8,24,76,9,13,41,45,49,77,89,109,113,129,133,165,169,201,205],[2084,2,155649,8388611,73857,265,81,2084,2084,524294,1048612,1073741836,2147483668,4198401,4099,12417,265,81,2129922,33834624,268436744,536872016,4295000578,8589934602,16777234,904,67108944,134217752]),
([pw0,pw1,pw2,pw3,pw8,pw22,pw45,pw157],[56,164,1,8,40,168,172,57,3,41,65,69,73,132,176,5,77,81,89,24,180,9,13,17,21,61,85,97,101,105,113,149,209,213,217],[32774,32774,2097158,4194310,32774,8388614,16777222,2147483793,4294968209,152,9,3249,69841,67265280,8590205192,925953,3104,134221888,33571336,269501185,3104,69696,16,536870952,17179869256,3105,69697,1073741920]),
([pw159,pw0,pw1,pw2,pw3,pw8,pw45,pw157],[40,8,184,188,192,160,1,65,73,221,196,5,149,3,76,37,4,24,9,13,53,57,61,77,81,109,113,129,133,165,169,201,225,229,233],[2116,2,172033,74241,4194307,137,273,2116,2116,262212,524294,536870924,1073741844,2101249,12801,4099,137,273,16827936,12884918306,134217896,268435760,2148533250,1672,8388880,17179869194,33554450,67108888]),
([pw0,pw1,pw2,pw3,pw14,pw8,pw45,pw157],[160,200,1,4,24,208,212,33,61,204,65,81,3,73,5,77,105,40,140,9,13,17,21,25,45,57,69,85,109,113,137,157,237,241,245,249],[16390,16390,524294,16390,1048582,2097158,4194310,2147485841,16781449,8523905,33559425,4294968481,8589942977,2072,9,17179875601,67111985,34359748689,16,134218504,1064,32840,1074008833,66593,41025,67360,268444480,536871008]),
([pw128,pw0,pw1,pw2,pw3,pw8,pw45,pw157],[24,216,220,224,4,5,69,253,257,132,228,1,157,3,33,49,8,40,76,200,9,13,29,41,57,81,105,113,121,125,141,165,169,201,261],[2082,155649,4194305,524289,73857,69,265,2082,2082,1048610,2097186,2147483654,4294967306,33558529,8421392,17057408,268436036,536871688,4113,12417,69,265,8589968400,1073741844,17179869208,67108932,1416,134217740]),
([pw0,pw1,pw2,pw3,pw8,pw23,pw45,pw157],[160,232,1,8,24,240,244,33,49,236,89,3,65,73,5,69,97,45,40,180,9,13,17,21,57,93,101,109,113,161,233,237,241,265],[16390,16390,1048582,2097158,16390,4194310,8388614,536872081,134017,16779401,395393,2147487905,4294975681,8589937937,1048,9,37937,74833,33555208,67635969,37664,74560,16,1073741864,134217800,36897,73793,268435552]),
([pw129,pw0,pw1,pw2,pw3,pw8,pw45,pw157],[24,248,252,256,5,269,8,132,69,97,260,1,33,161,3,76,4,40,232,9,13,29,45,53,57,89,105,113,121,125,141,165,169,201,217],[2066,151553,2097153,81953,262145,261,521,2066,2066,524306,1048594,2147483654,4294967306,33562625,4232352,16814208,268435844,536871560,24609,8257,261,521,8598324320,1073742084,1576,67108932,17179869256,134217740]),
([pw0,pw1,pw2,pw3,pw8,pw24,pw45,pw157],[4,264,1,8,272,276,180,268,65,69,73,77,3,5,9,25,29,49,61,24,40,13,17,21,33,37,41,45,53,81,85,93,97,105,109,113],[8198,8198,16390,2097158,16390,4194310,8388614,50434048,67239937,268697608,135303360,784,3104,1073872897,2147745800,537465024,784,4294968352,9,9,273,2081,1,8589934616,17179869224,976,3296,34359738416])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p17_D9 : List StD := [
([pw1,pw160,pw2,pw3,pw8,pw45,pw157],[24,40,5,45,81,20,280,284,288,292,53,101,41,77,141,1,9,13,17,21,25,29,57,73,89,105,109,113,117,273,277,281,285,3],[37,268435491,1048586,4194314,536870922,1073741834,32801,65541,131077,262149,524293,2097169,16777233,2147483665,4294967313,8589941952,22848,8399424,33572224,67118720,134218496]),
([pw0,pw1,pw2,pw3,pw161,pw8,pw45,pw157],[140,296,24,1,157,40,48,45,304,29,53,300,5,9,137,12,16,13,17,21,57,69,73,89,113,217,273,277,281,285],[4106,4106,8202,8202,131082,262154,524298,534,224,96,1048736,67109024,134217888,532,532,8388628,268435476,536870932,4,1089,65,65,17409,2131969,4260097,17409,33554689,16779520]),
([pw0,pw1,pw2,pw161,pw8,pw45,pw157],[296,1,24,185,40,45,140,300,304,308,137,5,29,53,73,9,13,17,21,25,41,57,69,89,105,109,113,205,261,273,277,281,285],[2051,2051,32771,65539,131075,262147,4109,524336,2097200,536870960,1073741872,4108,8388620,2147483660,4294967308,1058368,138412224,268452160,16787072,33572608,67109248]),
([pw0,pw1,pw2,pw3,pw8,pw162,pw45,pw157],[180,312,40,1,149,24,81,41,44,25,316,320,5,13,89,101,12,16,9,17,21,29,45,69,73,113,273,277,281,285,289],[4106,4106,262154,8202,8202,524298,1048586,534,4194324,532,532,67108884,134217748,2097248,16480,16480,268435552,536871008,385,32897,32897,1073741953,4,257,257,8455169,16910337,33557504]),
([pw0,pw1,pw2,pw3,pw162,pw45,pw157],[180,312,1,40,293,24,41,81,316,320,5,25,77,101,137,141,9,13,17,21,29,45,53,73,113,217,225,273,277,281,285],[1030,1030,65542,131078,262150,524294,2074,2097176,2072,134217752,268435480,1048801,67109025,536871072,1073741984,4218945,41281,8393281,49409,33559041,16777984]),
([pw0,pw1,pw2,pw3,pw8,pw163,pw157],[324,1,24,40,297,45,328,332,336,340,41,137,5,53,77,81,9,13,17,21,25,57,69,73,89,105,109,113,141,273,277,285,3],[4099,4099,65539,131075,262147,524291,29,1048616,2097192,536870952,1073741864,32788,16777236,32788,2147483668,4294978752,272631168,8406656,33564992,67127872,134218496]),
([pw0,pw1,pw2,pw3,pw8,pw45,pw164],[344,1,40,301,24,81,348,352,356,360,41,137,5,25,53,77,9,13,17,21,29,45,57,69,73,89,105,109,113,141,273,281,285,3],[4099,4099,65539,131075,262147,524291,8205,2097164,4194316,1073741836,8204,1048624,33554480,2147483696,4294967344,8589954240,545260928,16811648,67127616,134253120,268436224]),
([pw0,pw158,pw1,pw2,pw3,pw8,pw24,pw45,pw157],[364,1,44,48,372,376,380,3,140,5,9,45,77,81,141,180,264,268,368,13,17,21,25,29,37,57,69,73,89,105,109,113,117,121,125,129,133],[65667,515,515,1027,524291,1027,1048579,2097155,262145,16777217,265,32773,131329,145,161,4294967361,2120,33554500,4196416,8589934672,17179869280,8201,268435461,8396801,34359738385,68719476769,12,4,16408,4136,8,536870932,1073741860,67125264,134221856,2147483696]),
([pw165,pw1,pw2,pw10,pw3,pw8,pw45,pw157],[76,24,40,384,41,388,392,9,33,65,97,52,37,132,101,396,1,13,17,21,53,73,105,109,113,117,145,149,153,157,161,297,3],[2050,2052,2048,65689,131201,262273,524417,33558791,2,67109149,134217989,549,268435717,4,536875035,1073745923,2147483683,1091,8217,8193,545,1089,4296065048,16952,2098264,4194848,8389696,16777312]),
([pw165,pw1,pw2,pw3,pw8,pw45,pw157],[404,24,40,400,41,305,76,160,9,325,52,408,412,416,53,77,101,141,1,13,17,21,33,73,105,109,113,309,313,317,321,329,333,337,341,3],[1026,1028,262489,524609,1048897,2097473,4195367,134217789,268435493,536870949,1073741861,2147484314,4294967938,8589935234,17179869826,34359822360,200728,8429592,16930816,33613824,67121152]),
([pw0,pw1,pw2,pw3,pw166,pw8,pw45,pw157],[160,420,1,424,428,37,72,45,5,33,73,105,109,221,8,180,432,9,13,17,21,25,29,49,69,81,113,137,149,153,161,181,261,345,3],[262,262,131078,17179869191,262150,524294,1048582,673,515,2097153,268435585,2147483657,536871041,33554465,4194305,1073741857,8589934633,1073,65537,8396864,8264,4294967376,134266881,2057,4113,16779272,5136,67108888]),
([pw15,pw0,pw1,pw2,pw3,pw8,pw45,pw157],[76,72,432,448,452,436,444,53,160,440,1,73,193,5,9,45,69,81,180,13,33,41,77,105,109,113,141,149,161,165,169,181,249],[17412,34,514,258,266433,65545,2065,9476,9476,17412,525316,536870924,1073741844,1081893,32771,134222529,2147484169,2577,131362,268567008,65577,4294967345,2097346,67108874,4194322,8392904,16779472,33554456]),
([pw0,pw1,pw2,pw3,pw8,pw167,pw45,pw157],[180,456,1,76,472,476,460,33,49,65,61,73,89,5,37,69,97,101,464,468,480,9,13,17,21,77,85,93,113,141,349,353,3],[8198,8198,2097158,4194310,4294967303,8388614,16777222,282824,1073742089,1161,524289,33432,2147485864,67109185,134234177,1048577,37456,71776,131329,131329,529,65569,9,1553,3105,536870929,33554465,268435504]),
([pw168,pw0,pw1,pw2,pw3,pw8,pw45,pw157],[76,180,484,488,492,57,221,1,33,69,73,89,13,37,97,53,61,65,113,165,169,185,201,357],[4228,289,10241,67,65539,521,1041,165,2053,8388614,4228,524300,1048596,293,67,289,131081,1041,2097155,10241,521,16401,4227138,74,16402,522,1042,262168]),
([pw0,pw1,pw2,pw10,pw3,pw8,pw24,pw45,pw157],[496,5,364,380,500,33,504,37,73,65,80,49,61,69,72,180,97,132,1,9,145,157,8,76,160,268,13,17,21,41,53,77,85,93,105,109,113,117,141,149,153,161,3],[262179,262147,4398046511107,524291,67108867,524291,134217731,268435459,137438953644,4,1050664,549755818024,1179688,8760,1099511628072,8,4297064580,2207613190276,18874500,8852,65988,536922112,1077972992,42106880,274877907472,2147483968,17408,1024,10768,67904,16384,17179874320,34359743808,8720,65856,68719476816]),
([pw0,pw1,pw2,pw3,pw169,pw8,pw45,pw157],[76,508,1,96,512,29,45,160,516,40,132,520,5,33,157,49,109,137,221,180,9,13,17,21,69,73,89,105,113,129,149,153,181,189,261,285],[4102,4102,1048582,4102,2097158,4194310,8388614,24673,41033,8265,1073742401,4294967889,2147484225,16553,16545,67109025,9126805681,34359738529,1,294920,262168,17179869448,658432,16778256,66816,134350864,33622272,268435728]),
([pw0,pw1,pw2,pw3,pw8,pw170,pw45,pw157],[180,76,132,524,1,532,29,49,57,69,5,33,61,101,536,16,92,528,9,13,17,21,77,113,153,161,285,289,349,361],[1048,1048,262168,524312,1048,1048600,2097176,33556802,268435843,6147,133123,806,16777478,536870983,71,71,614,67108934,8321,8321,8225,134217857,2,4641,69633,545,4243457,8405024]),
([pw11,pw0,pw1,pw2,pw3,pw8,pw24,pw45,pw157],[380,92,96,368,548,552,5,364,65,73,1,49,61,97,9,33,69,160,180,264,268,540,544,13,29,81,85,93,105,109,113,145,165,169,173],[525384,2097280,4194305,2053,4099,1310721,273,545,1096,1096,16460,8388682,16456,4294967384,8589934696,17179902081,2053,4099,2147516417,273,545,67111044,134221954,50462848,65936,8864,6,2,276,8228,4,268435474,536870946,65808,8736,1073741872]),
([pw0,pw1,pw2,pw3,pw171,pw8,pw45,pw157],[160,556,1,25,37,560,572,116,568,5,73,137,45,53,81,105,180,564,9,13,17,21,57,77,85,109,113,161,173,205,273,277,365],[518,518,262150,518,524294,1048582,2097158,268435481,4105,4105,4194313,1073741833,2147483657,16401,16401,134217745,4294967313,1073,131073,16787840,536871104,8388768,67841,32833,1057,43328,33555488,67108960]),
([pw0,pw1,pw2,pw3,pw8,pw172,pw45,pw157],[160,180,576,1,25,37,580,5,73,101,584,41,57,89,12,112,9,13,17,21,45,53,93,113,141,157,173,261,273,277,365],[140,140,65548,131084,140,262156,524300,67108913,1048593,4113,4113,268435473,536870929,33554465,8225,8225,1073741857,353,2562,515,2562,134217794,2097155,4227074,322,16794625,321,8389696]),
([pw127,pw0,pw1,pw2,pw3,pw8,pw24,pw45,pw157],[364,112,116,588,592,596,1,97,69,5,65,85,93,380,9,37,73,132,180,264,268,544,13,25,29,45,49,61,105,109,113,157,165,169,173],[524872,2097153,16777217,2053,4099,1310721,273,161,584,584,16460,4194378,16456,4294967384,8589934696,17179910145,67110916,134221826,42082304,1296,65696,2053,4099,2147516417,273,161,6,2,1044,164,4,268435474,536870946,1296,65696,1073741872]),
([pw0,pw2,pw3,pw12,pw8,pw22,pw45,pw157],[132,600,5,136,180,81,608,612,1,45,29,69,89,177,193,604,9,13,17,21,53,57,77,109,113,209,221,261,281,285,369],[262,65542,262,131078,262,262150,524294,1057,1057,4129,4129,268435489,536870945,32769,24584,1073742353,100663312,134217808,25,25,2099329,8388673,1048585,24584,24,2689,4194881,16777408]),
([pw159,pw0,pw2,pw3,pw12,pw8,pw45,pw157],[180,616,620,624,160,132,1,73,221,5,29,137,145,268,37,45,57,69,109,113,129,133,141,165,169,177,181,185,189,209,261,357,369,373,377],[578,36865,4294971649,8193,33554433,67108869,137,578,2147483651,578,67,8388614,16777226,134218001,82992,1073,269484084,2097304,17,9126805761,261,1073741833,17179871265,4325412,262280,2053,137,524300]),
([pw0,pw1,pw2,pw12,pw14,pw8,pw45,pw157],[132,160,628,1,45,632,5,636,221,269,69,73,85,185,296,13,17,21,25,29,49,105,109,113,361,369,381],[76,76,76,76,32780,65548,131084,67117073,262145,33554451,19,19,19,16785411,524291,3,3,3,16387,4609,1569,4609,1048834,290,2434,2098208,4196480,8388768]),
([pw16,pw0,pw1,pw2,pw3,pw8,pw45,pw157],[132,160,640,1,33,96,652,5,45,49,137,656,660,53,644,648,9,13,17,21,37,73,105,109,113,221,269],[140,273,1048577,49153,3,3,3,140,140,65548,131084,262156,524300,273,273,19,19,19,3,3,3,3,9824,33554976,67109408,4205632,10490944,16783360]),
([pw0,pw1,pw2,pw3,pw12,pw8,pw23,pw45,pw157],[160,132,136,5,236,161,664,145,668,49,672,1,45,89,221,253,240,9,13,17,21,69,73,109,113,141,233,261,3],[6280,10280,131656,2120,262216,2120,524360,1048648,12448,17,16,135,4225,131,131,561,8225,37,5,35,35,1,532,16401,16912,134218512,32774,268435459,2163714,8388866,7,67109892,33028,33555457,4194561,16778496]),
([pw0,pw1,pw2,pw3,pw8,pw74,pw45,pw157],[132,676,1,680,684,136,29,57,69,5,37,45,77,193,688,9,13,17,21,25,53,73,81,89,113,133,137,141,217,3],[518,518,32774,65542,518,131078,262150,1089,2177,2177,524289,393,4241,4194369,8388673,1089,265,33554449,1056800,16385,134217992,2101264,67108897,8232,268435504,265,536870929,16777240]),
([pw63,pw0,pw1,pw2,pw3,pw8,pw45,pw157],[180,132,136,692,696,700,29,141,1,5,41,57,73,160,37,77,69,85,97,113,145,165,169,181,357],[776,2054,24643,8197,6,145,4129,776,776,16777225,13,2097176,4194344,1067074,1033,2055,8388754,36898,132163,5,65746,266338,1029,145,32801,5,5,524336]),
([pw0,pw1,pw2,pw173,pw3,pw8,pw45,pw157],[160,704,1,132,708,72,712,37,45,33,141,5,9,41,73,77,8,180,13,17,21,29,53,101,105,109,113,149,153,161,181,345,385],[2054,2054,4102,4102,262150,524294,1048582,905,769,769,134217985,1073741841,268435713,2097153,4294967465,536871049,2147483801,16585,8233,4390913,1041,32833,8396832,1072,32864,16778256,33570880,67108944]),
([pw0,pw1,pw2,pw3,pw8,pw174,pw45,pw157],[180,160,716,1,720,724,45,193,49,65,5,29,73,77,69,132,528,9,13,17,21,37,57,101,113,133,145,361,389],[1036,1036,131084,262156,1036,524300,1048588,69208130,4194567,195,65603,16978,12386,134217987,2179,34819,16914,33558562,268435841,8388865,529,8225,2,145,4257,529,8225,16777264]),
([pw13,pw0,pw2,pw3,pw8,pw22,pw45,pw157],[180,160,132,604,732,736,29,1,193,5,69,73,77,149,728,37,45,197,9,113,133,165,169,177,205,361,393,397,401],[648,41030,4,67109123,16385,140306,14370,648,262153,137,648,2097176,4194344,167772231,71,98374,132182,1050726,276824321,81921,16777233,4129,2,273,2337,1041,4129,524336]),
([pw0,pw1,pw2,pw3,pw14,pw8,pw22,pw45,pw157],[132,180,5,744,748,740,149,157,69,77,85,160,1,57,81,61,193,9,13,17,21,25,73,105,113,205,249,269,393,3],[12356,20612,132132,4132,262180,4132,524324,1048612,24768,1091,8257,268435459,2097153,329,593,3,2,131,16513,393,67109009,1,99330,134217731,33555466,1554,98306,536872961,8390920,4196880,2051,266,530,265,529,16777240]),
([pw0,pw1,pw2,pw3,pw22,pw23,pw45,pw157],[160,132,752,1,213,5,756,760,193,253,57,61,77,93,141,312,9,17,21,25,29,69,73,113,225,393,405],[44,44,65548,44,44,131084,262156,67109905,3,524291,33555459,3,3,19,16777235,1048577,19,19,8706,2305,2113600,4198528,32771,16962,8706,2305,4481,8388800]),
([pw175,pw0,pw1,pw2,pw3,pw8,pw45,pw157],[160,132,480,1,180,764,768,5,33,101,41,57,77,141,193,9,13,17,21,37,61,73,113,217],[140,2305,524289,3,3,3,3,140,140,32780,65548,131084,262156,2305,3,261,3,3,3,3,3,3,1066512,9776,2101840,24624,8392784,4194400]),
([pw65,pw0,pw1,pw2,pw3,pw8,pw45,pw157],[180,132,688,780,776,29,53,77,1,193,5,69,101,45,12,16,144,160,772,9,37,73,93,97,113,145,165,169,181,189,269],[1284,327681,131107,3,577,18449,32905,1284,1284,524293,261,67108884,134217740,34611234,12291,579,268437522,2097290,1073745923,4194339,536873010,8388778,577,4113,137,577,201,16777240]),
([pw0,pw1,pw2,pw176,pw3,pw8,pw45,pw157],[160,180,784,1,788,792,37,57,76,65,33,73,5,13,41,101,137,9,17,21,29,53,77,109,113,145,153,157,409],[4108,4108,8204,131084,8204,262156,524300,1217,1153,33554561,1153,529,67108993,1048577,134217793,268435523,593,2145,16643,257,273,289,2211842,33298,4196386,66066,8390690,16777264]),
([pw0,pw1,pw2,pw3,pw177,pw8,pw45,pw157],[180,160,796,1,800,804,45,61,65,73,221,5,29,37,57,69,77,76,120,9,13,17,21,113,133,137,145,185,389],[2060,2060,524300,2060,1048588,2097164,4194316,67121218,17475,278595,195,33106,66146,134218755,139267,4227,33042,16777762,2,268436609,1041,65569,33554561,273,545,401,673,8388656]),
([pw178,pw0,pw1,pw2,pw3,pw8,pw45,pw157],[160,132,808,5,37,116,1,49,81,816,820,221,564,812,9,13,17,21,33,69,73,105,109,113,269],[76,262145,273,12289,3,3,3,76,76,16396,32780,65548,131084,273,3,3,3,3,273,19,19,19,2208,2208,16777376,2621952,5243904,8390144]),
([pw0,pw1,pw3,pw14,pw8,pw23,pw45,pw157],[160,824,1,45,236,832,180,836,81,5,73,25,57,265,269,828,9,13,17,21,53,69,89,105,113,141,205,225,273,277],[518,65542,518,131078,518,262150,524294,2057,2057,4105,4105,268435465,536870921,32769,24592,273,67108912,24592,134217793,273,8388641,4195457,1048641,2097248,1216,33554721,1409,16777376]),
([pw129,pw0,pw1,pw3,pw14,pw8,pw45,pw157],[180,840,848,852,132,160,5,69,269,1,45,77,157,844,9,25,73,81,89,105,113,121,125,137,165,169,205,229,241,245,249,265,361,413],[578,135169,4294971649,8193,536870913,133,1073741833,578,16387,578,67,16777222,33554442,1297,295984,1073,2097300,272629816,17,10737418497,67108869,265,142606369,524420,67624,133,2057,1048588]),
([pw0,pw1,pw2,pw3,pw8,pw67,pw45,pw157],[160,856,1,25,860,864,236,89,5,73,141,33,81,269,868,9,13,17,21,29,45,57,101,105,109,113,273,277,3],[262,262,32774,65542,262,131078,262150,2057,1048585,2097161,2057,67108873,134217737,4225,4225,524289,1169,673,8258,4194369,1104,8288,16385,8389648,16777760,268435473,545,33554480]),
([pw68,pw0,pw1,pw2,pw3,pw8,pw45,pw157],[180,160,868,872,876,25,41,5,69,77,1,65,81,269,132,33,193,9,49,73,113,157,165,169,249],[1156,49187,20483,8257,2,265,529,1156,1156,131077,133,4194316,8388628,2134050,262243,65571,2346,524850,69,69635,2314,16777746,8257,2057,8257,265,529,1048600]),
([pw0,pw1,pw179,pw2,pw3,pw8,pw45,pw157],[132,880,1,884,72,888,33,81,76,37,69,5,41,101,417,13,17,21,25,73,105,109,113,149,153,161,249,261,349],[2054,16390,2054,16390,32774,65542,131078,262145,641,268435537,8388673,1097,16777281,641,4113,257,265,257,641,33554561,1033,67108897,12304,8216,134217776,1049608,2621472,4194344]),
([pw0,pw1,pw2,pw3,pw8,pw180,pw45,pw157],[76,180,892,236,1,25,132,900,904,81,5,85,97,141,253,33,69,89,896,9,13,17,21,45,57,73,101,113,157,273,277,421],[1044,1044,524308,1048596,1044,2097172,4194324,268468769,8388705,16777313,32865,536871009,1073741921,133133,147979,262667,74369,33559297,2147485706,67110922,8328,4360,1,82050,16642,8322,4354,134218112]),
([pw128,pw0,pw1,pw3,pw8,pw23,pw45,pw157],[180,132,160,828,912,916,25,5,253,1,69,73,141,161,908,33,81,257,113,121,165,169,225,245,261,357,369,425,429],[648,41030,4,4194563,16385,13330,141346,648,33554441,137,648,1048600,2097192,201326663,71,98374,525398,133222,276824321,81921,4113,16777249,2,1297,289,4113,2081,262192]),
([pw27,pw0,pw1,pw2,pw3,pw8,pw45,pw157],[160,132,180,468,5,37,49,920,924,1,89,77,101,141,193,9,17,21,33,61,73,113,217,433],[536,262145,1057,71,3,3,3,536,536,32792,8388636,65560,131096,1057,3,7,3,3,35,1057,35,35,544836,12484,1050948,24708,4196612,2097536]),
([pw71,pw0,pw1,pw2,pw3,pw8,pw45,pw157],[180,160,928,932,936,25,53,141,5,81,1,73,253,132,221,12,16,33,61,65,69,113,157,165,169,241,249,261,357,425],[1284,8227,8707,2,4161,32905,67601,1284,1284,268435461,261,8388620,16777236,4325922,536887331,262179,524458,33556530,16899,579,1048714,67110930,4161,137,134217745,201,4161,2097176]),
([pw0,pw1,pw181,pw2,pw3,pw8,pw45,pw157],[132,180,940,1,944,76,948,33,69,89,37,41,97,5,137,437,9,17,21,25,53,73,101,113,141,145,153,157,217,441],[8204,32780,8204,65548,32780,131084,262156,524289,1537,33554561,536871043,401,67108993,1537,2083,33,49,33,134218241,1537,273,4161,5261314,16777490,2103362,16658,268439618,8388688]),
([pw0,pw1,pw2,pw3,pw182,pw8,pw45,pw157],[180,76,952,1,25,81,132,956,960,93,5,69,97,269,33,141,200,9,13,17,21,45,73,113,137,157,273,277,421],[1036,1036,131084,1036,262156,524300,1048588,33570866,2097235,16467,83,67108946,134217810,8227,65571,547,34978,4198690,2,268444161,32897,8449,16777729,2177,4353,2689,4865,8388992]),
([pw183,pw0,pw1,pw2,pw3,pw8,pw45,pw157],[132,180,964,976,980,417,728,1,29,41,77,141,53,81,968,972,25,37,105,113,129,133,165,169,213,217,221,433],[164,2,8449,16899,36867,2057,1041,164,164,164,134217766,4194316,8388628,131329,579,69635,2057,1041,8451,16777475,1048585,2097169,67108934,2634,1618,264202,33555474,524312]),
([pw75,pw0,pw1,pw2,pw3,pw8,pw45,pw157],[160,984,1004,1008,9,908,25,77,141,180,37,1,45,988,992,996,1000,13,29,57,81,109,113,121,125,165,169,229,233,269,397],[2066,4161,1048577,24577,98305,261,137,19,19,2066,131090,33554438,67108874,263233,4161,524353,8388613,16777225,1073742881,134219265,261,137,536870946,292,168,268436228,2097800,4194316])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p17_D8 : List StD := [
([pw1,pw160,pw2,pw3,pw8,pw24,pw45,pw157],[364,5,277,380,29,280,284,1012,1016,1,9,25,45,77,81,141,13,17,21,57,69,73,89,105,109,113,117,273,281,285],[2566,67108893,4108,524300,4108,134217740,2060,515,1027,65539,1027,131075,262147,16401,4194321,16401,268435473,536870929,96,64,32928,8480,32,8388800,16777536,1081472,2105600,33554816]),
([pw0,pw1,pw2,pw3,pw8,pw24,pw163,pw157],[5,277,297,364,41,53,328,332,1024,1028,380,1020,29,1,9,25,45,77,81,141,160,324,13,17,21,49,57,61,69,73,89,105,109,113,273,285,445,449],[40963,12293,68719493137,137443147809,2115585,8390657,16779265,4110,33619986,201326626,1115138,17179870210,33794,262172,1073741868,262156,4108,34359738380,192,64,524688,131728,128,2147484000,4294967904,268960000,537002496,8589935360]),
([pw0,pw1,pw2,pw3,pw8,pw24,pw45,pw164],[1024,5,277,281,380,41,53,348,352,1036,1032,336,1,9,25,29,45,77,81,141,344,13,17,21,57,69,73,85,89,93,105,109,113,273,285,301,445,449],[20486,36874,68719484962,137441050690,1057794,4195330,8389634,34359738396,65588,16777300,65556,8589934612,16404,134479912,805306440,264201,32777,17179869193,384,128,524577,131872,256,1073742017,2147484352,34080769,67240448,4294967809]),
([pw165,pw1,pw2,pw10,pw3,pw8,pw24,pw45,pw157],[73,5,65,33,37,69,97,384,1,9,53,145,157,76,160,264,13,41,49,61,77,101,105,109,113,117,141,149,161,165,169,305,329,353,453],[258,258,32768,514,65538,514,17716740098,1073741827,33554456,2147483648,2056,134217736,2056,44,8589934601,4294967296,4112,268435472,4112,52,65,393216,525312,24576,67108868,1048577,1152,2097152,36,65,128,4194308,8388609,36,65,16777221]),
([pw165,pw1,pw2,pw3,pw8,pw24,pw45,pw157],[5,77,141,305,329,41,53,408,1040,1044,69,73,76,400,404,1,9,33,37,49,61,309,325,160,13,17,21,65,85,93,97,105,109,113,313,317,321,333,337,341],[163849,294929,589857,17825857,86017,33555461,67110915,393240,2621480,17180917832,2117640,34493956108,68719478794,272629808,137975824464,12587024,274877907988,550829555730,8320,128,1316,2594,8192,2147484100,4294968002,1284,2562,8589935366]),
([pw184,pw1,pw2,pw3,pw8,pw45,pw157],[160,400,404,457,420,329,1,305,140,1048,69,137,461,1052,13,17,21,53,333,337,341,465,469,473],[145,17,26,16452,32836,65604,163,145,5,5,5,11,262177,524321,1048609,4106,4106,2097162,134912,4196608,8398336]),
([pw185,pw1,pw2,pw3,pw8,pw45,pw157],[160,404,329,456,180,408,1,305,1056,69,101,477,481,1052,9,13,17,21,41,89,289,325,337,341,473],[137,9,16450,32778,65602,131138,135,3,137,3,3,2097157,524293,4194309,8388613,6176,263952,1049616,6176,48,16786176]),
([pw0,pw1,pw2,pw3,pw186,pw8,pw45,pw157],[5,49,73,93,145,161,69,1068,485,489,25,29,160,1072,1084,493,497,4,1052,1076,1080,1,0,16,1060,1064,9,13,17,21,97,109,113,273,277,281,285,289,393,417,501],[2098193,2099233,67109123,549760270337,134218249,268468289,536936453,3120,1298,50463760,274877915288,8589942864,17179934740,528418,10400,2600,34359775264,68719480868,655618,778,33090,137439019014,648,1099512938560,1082146820,712,2147500172,4296032324]),
([pw187,pw0,pw1,pw2,pw3,pw8,pw45],[404,132,1088,1092,241,1,5,41,53,29,37,45,505,1084,1096,17,69,185,193,213,221,281,357,433,509,513,517],[97,2065,1538,4228,16777480,33644544,97,97,4194309,8388617,32801,531,2065,281,67108881,131078,524298,2098178,4228,1048708,262408]),
([pw0,pw1,pw2,pw3,pw188,pw8,pw45,pw157],[5,61,73,85,149,157,69,485,489,1104,1112,25,29,160,1084,1100,493,497,1052,1080,1,9,0,16,648,1108,13,17,21,65,113,217,273,277,281,285,289,369,521],[1050641,1052705,2097289,6553601,67109123,134283329,268566533,6192,137438986776,50334224,2322,4294967888,8590065684,4264,37408,9250,17179942944,34359746596,32904,394,65736,68719607820,1282,537657408,274886311940,1346,2147501062,1074282564]),
([pw189,pw0,pw1,pw2,pw3,pw8,pw157],[1080,69,1116,1120,33,157,25,445,449,493,1124,1128,1,21,41,45,53,57,81,105,253,269,277,473,525],[515,83,515,515,524291,8388611,81,262177,16516,65800,15360,81,32773,131081,4194321,37,297,16777249,140,2097284,1048840])]
def p17_D7 : List StD := []
theorem p17_I7 : LevelN true p17_T 7 p17_D7 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p17_C8x0 : levelOK true p17_T p17_t 7 (p17_D7.map Prod.fst) ((p17_D8.drop (0*32)).take 32) = true := by decide +kernel
theorem p17_I8 : LevelN true p17_T 8 p17_D8 := levelStep p17_B p17_W p17_I7 (chunks 32 p17_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p17_C8x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p17_C9x0 : levelOK true p17_T p17_t 8 (p17_D8.map Prod.fst) ((p17_D9.drop (0*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p17_C9x1 : levelOK true p17_T p17_t 8 (p17_D8.map Prod.fst) ((p17_D9.drop (1*32)).take 32) = true := by decide +kernel
theorem p17_I9 : LevelN true p17_T 9 p17_D9 := levelStep p17_B p17_W p17_I8 (chunks 32 p17_D9 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p17_C9x0
  · exact p17_C9x1
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p17_C10x0 : levelOK true p17_T p17_t 9 (p17_D9.map Prod.fst) ((p17_D10.drop (0*32)).take 32) = true := by decide +kernel
theorem p17_I10 : LevelN true p17_T 10 p17_D10 := levelStep p17_B p17_W p17_I9 (chunks 32 p17_D10 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p17_C10x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p17_C11x0 : levelOK true p17_T p17_t 10 (p17_D10.map Prod.fst) ((p17_D11.drop (0*32)).take 32) = true := by decide +kernel
theorem p17_I11 : LevelN true p17_T 11 p17_D11 := levelStep p17_B p17_W p17_I10 (chunks 32 p17_D11 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p17_C11x0
  ))
theorem p17_L : LowN true p17_R p17_T 12 := lowSearch p17_B p17_I11 (by decide +kernel)
def ptopT : Nat := 0xfffffffffffffffefffffffffffefffcfffffffeffffffeefefefafaeeee0000
def ptopR : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]
def ptopE : List (Nat × Nat × Nat) := [(0,16,17),(1,16,18),(2,32,36),(3,64,72),(4,1,17),(5,1,33),(6,1,65),(7,2,130)]
theorem ptopB : baseOK ptopT ptopR ptopE = true := by decide +kernel
def ptopZ : List SliceD := [(pw5,12,[2, 5, 7, 4, 6, 1, 0])]
theorem ptopY : ∀ s ∈ ptopZ, SliceN true ptopR ptopT s := by
  unfold ptopZ
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) ptopB p17_B p17_L (by decide +kernel),by simp⟩
def ptopC : List (Nat × List Nat) := [(0,[])]
def ptopt : Tabs := (ptopC.map (mkCut true ptopZ),[],[],[[]])
theorem ptopW : TabsP true ptopR ptopT ptopt := ⟨cutsGood ptopY (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD12 : List StD := [
([pw0,pw1,pw2,pw3,pw8,pw45,pw157,pw190],[0],[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])]
def ptopD11 : List StD := []
theorem ptopI11 : LevelN true ptopT 11 ptopD11 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC12x0 : levelOK true ptopT ptopt 11 (ptopD11.map Prod.fst) ((ptopD12.drop (0*32)).take 32) = true := by decide +kernel
theorem ptopI12 : LevelN true ptopT 12 ptopD12 := levelStep ptopB ptopW ptopI11 (chunks 32 ptopD12 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC12x0
  ))
theorem ptopL : LowN true ptopR ptopT 13 := lowSearch ptopB ptopI12 (by decide +kernel)

def theInputs : List Sig := rootsW [0,1,2,3,4,5,6,7]
def graph : Sig := W ptopT
theorem graph_proper : proper graph := (baseOK_ok ptopB).prop
def sample (r : Row) (i : Fin 8) : Bool := bit r (theInputs.getD i.val zero)
theorem theList : List.ofFn (fun i : Fin 8 => theInputs.getD i.val zero) = theInputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = theInputs.map (bit r) := by
  rw [←theList,List.map_ofFn]
  rfl
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem theTable : ∀ r : Row, bit r graph = target (sample r) := by decide +kernel
theorem theEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates theInputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl
theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k theInputs.toFinset := by
  have b := baseOK_ok ptopB
  have goalEq : (execute C.gates theInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (theEval C legal C.output r).trans ((computes (sample r)).trans (theTable r).symm)
  have out := get_rep (u:=true) (execute C.gates theInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by
    change bit 0 (W ptopT) = false
    have := b.plain
    unfold plainWord at this
    simpa using this
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates theInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : theInputs.all plainWord = true := b.plainR
  rw [nrm_map ns] at sub
  have eq : S = theInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨r,s,hd,iso⟩ := b.ess a (List.mem_toFinset.mp ha)
      exact raw_required run theInputs a sub r s hd iso
  exact ⟨k,hk,eq ▸ run⟩
theorem excludes : Impossible true graph 12 theInputs.toFinset := by
  intro k small run
  have steps := list_run run theInputs (by decide +kernel) rfl
  obtain ⟨q, bank, built, hit, limit⟩ := contraction (observe_proper graph_proper)
    steps (theInputs.map observe) Reach.start (fun _ h => Or.inl h)
  have bound := ptopL q bank built hit
  omega
theorem replaceShort (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 8 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 8 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 14 ≤ gates.length
  · exact ⟨smallCircuit.gates,smallCircuit.output,witnessMonotone,(by simpa only [witnessSize] using big),witnessCorrect⟩
  by_cases mono : ∀ g ∈ gates, g.op ≠ GateOp.not
  · refine ⟨gates,o,?_,Nat.le_refl _,correct⟩
    intro g hg
    obtain ⟨ops,arity⟩ := fit g hg
    refine ⟨?_,arity⟩
    rcases ops with a | b | c
    · exact Or.inl a
    · exact Or.inr b
    · exact (mono g hg c).elim
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
  exact (excludes k (by omega) run).elim

end PEqualNP.Outside.L_meta_15070

theorem PEqualNP.Outside.L_meta_15070 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 3, 6, 4, 6, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact PEqualNP.Outside.L_meta_15070.replaceShort gates o fit correct
