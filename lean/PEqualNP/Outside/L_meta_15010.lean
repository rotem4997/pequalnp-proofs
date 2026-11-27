import PEqualNP.Defs

-- The live-set and restriction lemmas follow L-meta-10554, L-meta-10802, L-meta-1674, L-meta-670 and L-meta-1667.
-- The rectangle argument follows L-meta-8459.
namespace PEqualNP.Outside.L_meta_15010
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


def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.or, [2, 8]⟩,
    ⟨.or, [4, 8]⟩,
    ⟨.or, [0, 2]⟩,
    ⟨.or, [3, 11]⟩,
    ⟨.or, [4, 12]⟩,
    ⟨.and, [8, 4]⟩,
    ⟨.and, [9, 5]⟩,
    ⟨.and, [10, 6]⟩,
    ⟨.and, [13, 7]⟩,
    ⟨.or, [14, 15]⟩,
    ⟨.or, [18, 16]⟩,
    ⟨.or, [19, 17]⟩], 20⟩
theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel
theorem witnessSize : smallCircuit.gates.length = 13 := rfl
def pw0 : Nat := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def pw1 : Nat := 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc
def pw2 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
def pw3 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def pw4 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
def pw5 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def pw6 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
def pw7 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def pw8 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def pw9 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def pw10 : Nat := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc
def pw11 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
def pw12 : Nat := 0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc
def pw13 : Nat := 0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc
def pw14 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0
def pw15 : Nat := 0xfc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc
def pw16 : Nat := 0xf0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c
def pw17 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def pw18 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def pw19 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def pw20 : Nat := 0x5555555500000000555555550000000055555555000000005555555500000000
def pw21 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
def pw22 : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
def pw23 : Nat := 0x4444444444444444444444444444444444444444444444444444444444444444
def pw24 : Nat := 0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa
def pw25 : Nat := 0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa
def pw26 : Nat := 0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc
def pw27 : Nat := 0xfefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefe
def pw28 : Nat := 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e
def pw29 : Nat := 0xf4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4
def pw30 : Nat := 0x3232323232323232323232323232323232323232323232323232323232323232
def pw31 : Nat := 0xcccccccceeeeeeeecccccccceeeeeeeecccccccceeeeeeeecccccccceeeeeeee
def pw32 : Nat := 0x5454545454545454545454545454545454545454545454545454545454545454
def pw33 : Nat := 0xfcfc0000fcfc0000fcfc0000fcfc0000fcfc0000fcfc0000fcfc0000fcfc
def pw34 : Nat := 0xaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeae
def pw35 : Nat := 0xfe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe
def pw36 : Nat := 0xfefe0000fefe0000fefe0000fefe0000fefe0000fefe0000fefe0000fefe
def pw37 : Nat := 0xf4f40000f4f40000f4f40000f4f40000f4f40000f4f40000f4f40000f4f4
def pw38 : Nat := 0xc0c0c0caeaeaeae0c0c0c0caeaeaeae0c0c0c0caeaeaeae0c0c0c0caeaeaeae
def pw39 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def pw40 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def pw41 : Nat := 0x8888888888888888888888888888888888888888888888888888888888888888
def pw42 : Nat := 0x2222222222222222222222222222222222222222222222222222222222222222
def pw43 : Nat := 0x5050505050505050505050505050505050505050505050505050505050505050
def pw44 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa
def pw45 : Nat := 0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc
def pw46 : Nat := 0xff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88
def pw47 : Nat := 0xffff8888ffff8888ffff8888ffff8888ffff8888ffff8888ffff8888ffff8888
def pw48 : Nat := 0xffffffff88888888ffffffff88888888ffffffff88888888ffffffff88888888
def pw49 : Nat := 0xeeeeeeee00000000eeeeeeee00000000eeeeeeee00000000eeeeeeee00000000
def pw50 : Nat := 0xffffffffeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeeeffffffffeeeeeeee
def pw51 : Nat := 0xeeeeeeee00000000eeeeeeee00000000eeeeeeee00000000eeeeeeee
def pw52 : Nat := 0xffffffff44444444ffffffff44444444ffffffff44444444ffffffff44444444
def pw53 : Nat := 0x5555555544444444555555554444444455555555444444445555555544444444
def pw54 : Nat := 0xaaaaaaaaeeeeeeeeaaaaaaaaeeeeeeeeaaaaaaaaeeeeeeeeaaaaaaaaeeeeeeee
def pw55 : Nat := 0xffeeffeeff00ff00ffeeffeeff00ff00ffeeffeeff00ff00ffeeffeeff00ff00
def pw56 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa
def pw57 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa
def pw58 : Nat := 0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc
def pw59 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0
def pw60 : Nat := 0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00
def pw61 : Nat := 0xeeee0000eeee0000eeee0000eeee0000eeee0000eeee0000eeee0000eeee
def pw62 : Nat := 0xfa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa
def pw63 : Nat := 0x3333303033333030333330303333303033333030333330303333303033333030
def pw64 : Nat := 0x5555550055555500555555005555550055555500555555005555550055555500
def pw65 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def pw66 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def pw67 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0
def pw68 : Nat := 0x3030303030303030303030303030303030303030303030303030303030303030
def pw69 : Nat := 0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc
def pw70 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0
def pw71 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0
def pw72 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0
def pw73 : Nat := 0xffff4444ffff4444ffff4444ffff4444ffff4444ffff4444ffff4444ffff4444
def pw74 : Nat := 0xfafa0000fafa0000fafa0000fafa0000fafa0000fafa0000fafa0000fafa
def pw75 : Nat := 0xdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdc
def pw76 : Nat := 0xffffffff50505050ffffffff50505050ffffffff50505050ffffffff50505050
def pw77 : Nat := 0xeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaea
def pw78 : Nat := 0xffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0
def pw79 : Nat := 0xffffc0c0ffffc0c0ffffc0c0ffffc0c0ffffc0c0ffffc0c0ffffc0c0ffffc0c0
def pw80 : Nat := 0xffffffffc0c0c0c0ffffffffc0c0c0c0ffffffffc0c0c0c0ffffffffc0c0c0c0
def pw81 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcfffffcfcfffffcfcfffffcfcfffffcfc
def pw82 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfcfffffffffcfcfcfcfffffffffcfcfcfc
def pw83 : Nat := 0xfcfcfcfc00000000fcfcfcfc00000000fcfcfcfc00000000fcfcfcfc
def pw84 : Nat := 0xffffffff0c0c0c0cffffffff0c0c0c0cffffffff0c0c0c0cffffffff0c0c0c0c
def pw85 : Nat := 0xbabababababababababababababababababababababababababababababababa
def pw86 : Nat := 0xffff3030ffff3030ffff3030ffff3030ffff3030ffff3030ffff3030ffff3030
def pw87 : Nat := 0xaaaaeeeeaaaaeeeeaaaaeeeeaaaaeeeeaaaaeeeeaaaaeeeeaaaaeeeeaaaaeeee
def pw88 : Nat := 0xf0f0fcfcf0f0fcfcf0f0fcfcf0f0fcfcf0f0fcfcf0f0fcfcf0f0fcfcf0f0fcfc
def pw89 : Nat := 0xf0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c
def pw90 : Nat := 0xf0f0f0f0fcfcfcfcf0f0f0f0fcfcfcfcf0f0f0f0fcfcfcfcf0f0f0f0fcfcfcfc
def pw91 : Nat := 0xccccfcfcccccfcfcccccfcfcccccfcfcccccfcfcccccfcfcccccfcfcccccfcfc
def pw92 : Nat := 0xaaaaaaaafafafafaaaaaaaaafafafafaaaaaaaaafafafafaaaaaaaaafafafafa
def pw93 : Nat := 0xccccccccfcfcfcfcccccccccfcfcfcfcccccccccfcfcfcfcccccccccfcfcfcfc
def pw94 : Nat := 0xfefefefe00000000fefefefe00000000fefefefe00000000fefefefe
def pw95 : Nat := 0xaeaeaeae00000000aeaeaeae00000000aeaeaeae00000000aeaeaeae
def pw96 : Nat := 0xbaba0000baba0000baba0000baba0000baba0000baba0000baba0000baba
def pw97 : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
def pw98 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def pw99 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def pw100 : Nat := 0x22002200220022002200220022002200220022002200220022002200220022
def pw101 : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
def pw102 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
def pw103 : Nat := 0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00
def pw104 : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000
def pw105 : Nat := 0xddddddddccccccccddddddddccccccccddddddddccccccccddddddddcccccccc
def pw106 : Nat := 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000
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
def p2_T : Nat := 0xeee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8eee8
def p2_R : List Nat := [0, 1, 2, 3]
def p2_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem p2_B : baseOK p2_T p2_R p2_E = true := by decide +kernel
def p2_Z : List SliceD := [(pw3,4,[0, 1, 3])]
theorem p2_Y : ∀ s ∈ p2_Z, SliceN true p2_R p2_T s := by
  unfold p2_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p2_B p1_B p1_L (by decide +kernel),by simp⟩
def p2_C : List (Nat × List Nat) := [(0,[])]
def p2_t : Tabs := (p2_C.map (mkCut true p2_Z),[(5,4),(6,4),(3,2),(3,1),(6,2),(5,1),(10,2),(9,8),(9,1),(10,8)],[],[[]])
theorem p2_W : TabsP true p2_R p2_T p2_t := ⟨cutsGood p2_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p2_D4 : List StD := [
([pw0,pw1,pw2,pw4],[1,5,17,25,9,13,21,33,0,29,37],[51,85,649,102,1162,268])]
def p2_D3 : List StD := []
theorem p2_I3 : LevelN true p2_T 3 p2_D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p2_C4x0 : levelOK true p2_T p2_t 3 (p2_D3.map Prod.fst) ((p2_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p2_I4 : LevelN true p2_T 4 p2_D4 := levelStep p2_B p2_W p2_I3 (chunks 32 p2_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p2_C4x0
  ))
theorem p2_L : LowN true p2_R p2_T 5 := lowSearch p2_B p2_I4 (by decide +kernel)
def p3_T : Nat := 0xeae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8
def p3_R : List Nat := [0, 1, 2, 3]
def p3_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem p3_B : baseOK p3_T p3_R p3_E = true := by decide +kernel
def p3_Z : List SliceD := [(pw5,4,[0, 1, 2])]
theorem p3_Y : ∀ s ∈ p3_Z, SliceN true p3_R p3_T s := by
  unfold p3_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p3_B p1_B p1_L (by decide +kernel),by simp⟩
def p3_C : List (Nat × List Nat) := [(0,[])]
def p3_t : Tabs := (p3_C.map (mkCut true p3_Z),[(5,4),(6,4),(3,2),(3,1),(6,2),(5,1)],[],[[]])
theorem p3_W : TabsP true p3_R p3_T p3_t := ⟨cutsGood p3_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p3_D4 : List StD := [
([pw0,pw1,pw2,pw4],[0,1,5,17,9,13,21],[54,90,3,108,5,9])]
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
def p4_T : Nat := 0xeeeaece8eeeaece8eeeaece8eeeaece8eeeaece8eeeaece8eeeaece8eeeaece8
def p4_R : List Nat := [0, 1, 2, 3, 4]
def p4_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,2,10),(4,1,17)]
theorem p4_B : baseOK p4_T p4_R p4_E = true := by decide +kernel
def p4_Z : List SliceD := [(pw5,5,[0, 1, 2, 4])]
theorem p4_Y : ∀ s ∈ p4_Z, SliceN true p4_R p4_T s := by
  unfold p4_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p4_B p3_B p3_L (by decide +kernel),by simp⟩
def p4_C : List (Nat × List Nat) := [(0,[])]
def p4_t : Tabs := (p4_C.map (mkCut true p4_Z),[(5,4),(6,4),(3,2),(3,1),(6,2),(5,1),(10,2),(13,12)],[],[[]])
theorem p4_W : TabsP true p4_R p4_T p4_t := ⟨cutsGood p4_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p4_D5 : List StD := [
([pw0,pw1,pw2,pw4,pw6],[0,1,5,17,25,9,13,21,29],[102,170,275,3,204,5,5,25,9,17])]
def p4_D4 : List StD := []
theorem p4_I4 : LevelN true p4_T 4 p4_D4 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p4_C5x0 : levelOK true p4_T p4_t 4 (p4_D4.map Prod.fst) ((p4_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p4_I5 : LevelN true p4_T 5 p4_D5 := levelStep p4_B p4_W p4_I4 (chunks 32 p4_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p4_C5x0
  ))
theorem p4_L : LowN true p4_R p4_T 6 := lowSearch p4_B p4_I5 (by decide +kernel)
def p5_T : Nat := 0xeac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8
def p5_R : List Nat := [0, 1, 2, 3]
def p5_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,1,9)]
theorem p5_B : baseOK p5_T p5_R p5_E = true := by decide +kernel
def p5_Z : List SliceD := []
theorem p5_Y : ∀ s ∈ p5_Z, SliceN true p5_R p5_T s := by
  intro s h
  cases h
def p5_C : List (Nat × List Nat) := []
def p5_t : Tabs := (p5_C.map (mkCut true p5_Z),[(6,4),(3,1),(3,2),(9,12),(6,2),(9,1),(9,0),(6,12),(9,5)],[],[[]])
theorem p5_W : TabsP true p5_R p5_T p5_t := ⟨cutsGood p5_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p5_D3 : List StD := [
([pw0,pw1,pw2,pw4],[1,21,5,9,17,13,25,29,33],[5,56,74,5,131,274])]
def p5_D2 : List StD := []
theorem p5_I2 : LevelN true p5_T 2 p5_D2 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5_C3x0 : levelOK true p5_T p5_t 2 (p5_D2.map Prod.fst) ((p5_D3.drop (0*32)).take 32) = true := by decide +kernel
theorem p5_I3 : LevelN true p5_T 3 p5_D3 := levelStep p5_B p5_W p5_I2 (chunks 32 p5_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_C3x0
  ))
theorem p5_L : LowN true p5_R p5_T 4 := lowSearch p5_B p5_I3 (by decide +kernel)
def p6_T : Nat := 0xfeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeea
def p6_R : List Nat := [0, 1, 2, 3]
def p6_E : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6),(3,2,10)]
theorem p6_B : baseOK p6_T p6_R p6_E = true := by decide +kernel
def p6_Z : List SliceD := [(pw7,4,[1, 2, 3])]
theorem p6_Y : ∀ s ∈ p6_Z, SliceN true p6_R p6_T s := by
  unfold p6_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p6_B p1_B p1_L (by decide +kernel),by simp⟩
def p6_C : List (Nat × List Nat) := [(0,[])]
def p6_t : Tabs := (p6_C.map (mkCut true p6_Z),[(1,0),(6,4),(3,2)],[],[[]])
theorem p6_W : TabsP true p6_R p6_T p6_t := ⟨cutsGood p6_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p6_D4 : List StD := [
([pw0,pw1,pw2,pw4],[0,1,5,9],[15,3,3,1,5,1])]
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
theorem p6_L : LowN true p6_R p6_T 5 := lowSearch p6_B p6_I4 (by decide +kernel)
def p7_T : Nat := 0xfeeafcc8feeafcc8feeafcc8feeafcc8feeafcc8feeafcc8feeafcc8feeafcc8
def p7_R : List Nat := [0, 1, 2, 3, 4]
def p7_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,2,10),(4,1,17)]
theorem p7_B : baseOK p7_T p7_R p7_E = true := by decide +kernel
def p7_Z : List SliceD := [(pw8,4,[1, 2, 3]),(pw3,4,[0, 1, 3, 4]),(pw5,4,[0, 1, 2, 4]),(pw6,5,[0, 1, 2, 3]),(pw9,5,[1, 2, 3, 0])]
theorem p7_Y : ∀ s ∈ p7_Z, SliceN true p7_R p7_T s := by
  unfold p7_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p7_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p7_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p7_B p5_B p5_L (by decide +kernel),mkSlice (w:=16) p7_B p6_B p6_L (by decide +kernel),mkSlice (w:=0) p7_B p3_B p3_L (by decide +kernel),by simp⟩
def p7_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[])]
def p7_t : Tabs := (p7_C.map (mkCut true p7_Z),[(3,2),(17,16),(21,20),(25,24),(12,8),(6,4),(6,2),(12,4),(10,8),(10,2),(7,4),(12,5),(3,5),(3,1),(6,20),(17,1),(6,18),(21,5),(17,9),(12,9),(6,0),(17,5),(11,8),(3,9),(10,24),(10,18),(25,9),(10,0),(12,20),(12,0),(12,1),(17,0),(10,16),(22,2),(7,0),(6,16),(12,16)],[],[[]])
theorem p7_W : TabsP true p7_R p7_T p7_t := ⟨cutsGood p7_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p7_D6 : List StD := [
([pw0,pw1,pw2,pw4,pw6],[0,1,12,3,4,8,5,17,25,29,9,13,21,33,37],[67,1027,2051,67,4504,25128,5,952,5,5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p7_D5 : List StD := [
([pw0,pw1,pw2,pw10,pw4,pw6],[1,37,21,61,9,25,29,8,5,17,41,45,49,53,57,65,69,73,3],[1029,17,257,2051,17,4132,8192,70,16396,512,66,32808,262274,65544,131082]),
([pw11,pw0,pw1,pw2,pw4,pw6],[5,29,61,1,17,37,21,12,16,25,45,53,57,73,77,81,85],[9,2048,512,34,388,9,16401,1027,9,32848,34,4164,34,65556,8198]),
([pw0,pw1,pw2,pw4,pw12,pw6],[1,25,33,61,13,17,37,4,5,29,53,77,85,89,93,97,101,105,3],[8197,2051,17,257,17,38,16452,1024,32780,34,262274,4106,512,65608,131080]),
([pw13,pw0,pw1,pw2,pw4,pw6],[5,17,61,1,25,29,33,12,16,37,45,53,73,77,85,97,109],[9,2048,18,512,388,9,8195,1057,9,18,65632,32836,18,16390,4132]),
([pw0,pw1,pw2,pw4,pw14,pw6],[21,1,61,29,53,4,9,17,69,25,33,45,57,77,113],[17,8322,2058,66,66,17,1025,17,4101,40,512,388,32,16396,260])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p7_D4 : List StD := [
([pw15,pw0,pw1,pw2,pw6],[1,25,37,69,109,61,117,41,45,53,121,125,129],[261,532,70,44,145,1027,2057,82,4120,42]),
([pw16,pw0,pw1,pw4,pw6],[1,25,37,61,81,117,53,77,121,125,133,137,141,145],[131,82,38,1034,2065,261,521,52,4120,8204])]
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
def p8_T : Nat := 0xfeeafce8feeafce8feeafce8feeafce8feeafce8feeafce8feeafce8feeafce8
def p8_R : List Nat := [0, 1, 2, 3, 4]
def p8_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,2,10),(4,1,17)]
theorem p8_B : baseOK p8_T p8_R p8_E = true := by decide +kernel
def p8_Z : List SliceD := [(pw17,4,[0, 2, 3, 4]),(pw8,4,[1, 2, 3]),(pw3,4,[0, 1, 3, 4]),(pw5,5,[0, 1, 2, 4]),(pw6,5,[0, 1, 2, 3])]
theorem p8_Y : ∀ s ∈ p8_Z, SliceN true p8_R p8_T s := by
  unfold p8_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p8_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p8_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p8_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p8_B p3_B p3_L (by decide +kernel),mkSlice (w:=16) p8_B p6_B p6_L (by decide +kernel),by simp⟩
def p8_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[])]
def p8_t : Tabs := (p8_C.map (mkCut true p8_Z),[(6,4),(3,2),(3,0),(5,4),(25,24),(3,1),(6,2),(10,2),(10,0),(12,4),(17,16),(17,24),(6,20),(6,18),(17,1),(17,9),(5,1),(26,2),(10,16),(12,16)],[],[[]])
theorem p8_W : TabsP true p8_R p8_T p8_t := ⟨cutsGood p8_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p8_D6 : List StD := [
([pw0,pw1,pw2,pw4,pw6],[4,0,1,5,12,16,8,17,25,29,9,13,21,33,37,3],[1039,2057,137,137,37190,8726,39,17232,33,49])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p8_D5 : List StD := [
([pw0,pw1,pw2,pw10,pw4,pw6],[13,29,0,57,5,25,41,4,12,16,1,21,37,45,49,53,61,3],[17,17,65,8195,65,36,2048,6,17412,4,4098,32808,131330,648,65546])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p8_D4 : List StD := [
([pw15,pw0,pw1,pw2,pw6],[5,29,25,33,41,57,1,13,21,65,69,73,77],[19,266,518,1058,17,129,17,76,2088,4132])]
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p8_C5x0 : levelOK true p8_T p8_t 4 (p8_D4.map Prod.fst) ((p8_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p8_I5 : LevelN true p8_T 5 p8_D5 := levelStep p8_B p8_W p8_I4 (chunks 32 p8_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p8_C5x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p8_C6x0 : levelOK true p8_T p8_t 5 (p8_D5.map Prod.fst) ((p8_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p8_I6 : LevelN true p8_T 6 p8_D6 := levelStep p8_B p8_W p8_I5 (chunks 32 p8_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p8_C6x0
  ))
theorem p8_L : LowN true p8_R p8_T 7 := lowSearch p8_B p8_I6 (by decide +kernel)
def p9_T : Nat := 0xfeeefae8feeefae8feeefae8feeefae8feeefae8feeefae8feeefae8feeefae8
def p9_R : List Nat := [0, 1, 2, 3, 4]
def p9_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,1,17)]
theorem p9_B : baseOK p9_T p9_R p9_E = true := by decide +kernel
def p9_Z : List SliceD := [(pw17,5,[0, 2, 3, 4]),(pw3,5,[0, 1, 4, 3]),(pw5,5,[0, 1, 2, 4]),(pw9,5,[0, 2, 1, 3])]
theorem p9_Y : ∀ s ∈ p9_Z, SliceN true p9_R p9_T s := by
  unfold p9_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p9_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p9_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p9_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p9_B p2_B p2_L (by decide +kernel),by simp⟩
def p9_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[])]
def p9_t : Tabs := (p9_C.map (mkCut true p9_Z),[(3,1),(6,4),(5,1),(6,2),(9,1),(12,4),(17,1),(18,2),(18,24),(12,24),(18,10)],[],[[]])
theorem p9_W : TabsP true p9_R p9_T p9_t := ⟨cutsGood p9_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p9_D6 : List StD := [
([pw0,pw1,pw2,pw4,pw6],[0,8,12,4,1,5,21,29,9,13,17,25,33,37,41],[49,776,1090,2180,49,4099,133,74,8204,16390])]
def p9_D5 : List StD := []
theorem p9_I5 : LevelN true p9_T 5 p9_D5 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p9_C6x0 : levelOK true p9_T p9_t 5 (p9_D5.map Prod.fst) ((p9_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p9_I6 : LevelN true p9_T 6 p9_D6 := levelStep p9_B p9_W p9_I5 (chunks 32 p9_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p9_C6x0
  ))
theorem p9_L : LowN true p9_R p9_T 7 := lowSearch p9_B p9_I6 (by decide +kernel)
def p10_T : Nat := 0xeeeaece0eeeaece0eeeaece0eeeaece0eeeaece0eeeaece0eeeaece0eeeaece0
def p10_R : List Nat := [0, 1, 2, 3, 4]
def p10_E : List (Nat × Nat × Nat) := [(0,4,5),(1,4,6),(2,1,5),(3,2,10),(4,1,17)]
theorem p10_B : baseOK p10_T p10_R p10_E = true := by decide +kernel
def p10_Z : List SliceD := []
theorem p10_Y : ∀ s ∈ p10_Z, SliceN true p10_R p10_T s := by
  intro s h
  cases h
def p10_C : List (Nat × List Nat) := []
def p10_t : Tabs := (p10_C.map (mkCut true p10_Z),[(5,4),(10,9),(6,4),(6,2),(5,0),(10,3),(10,2),(17,1),(17,0),(5,1),(10,0),(17,3),(5,9),(6,18),(17,9)],[],[[]])
theorem p10_W : TabsP true p10_R p10_T p10_t := ⟨cutsGood p10_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p10_D4 : List StD := [
([pw0,pw1,pw2,pw4,pw6],[1,9,13,25,29,5,17,21,33,37,41,45,49,53,57],[35,69,137,273,518,1034,2066,4108,8212,16408])]
def p10_D3 : List StD := []
theorem p10_I3 : LevelN true p10_T 3 p10_D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_C4x0 : levelOK true p10_T p10_t 3 (p10_D3.map Prod.fst) ((p10_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p10_I4 : LevelN true p10_T 4 p10_D4 := levelStep p10_B p10_W p10_I3 (chunks 32 p10_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p10_C4x0
  ))
theorem p10_L : LowN true p10_R p10_T 5 := lowSearch p10_B p10_I4 (by decide +kernel)
def p11_T : Nat := 0xfefefeeafefcfec8fefefeeafefcfec8fefefeeafefcfec8fefefeeafefcfec8
def p11_R : List Nat := [0, 1, 2, 3, 4, 5]
def p11_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,1,9),(4,2,18),(5,1,33)]
theorem p11_B : baseOK p11_T p11_R p11_E = true := by decide +kernel
def p11_Z : List SliceD := [(pw18,5,[1, 2, 3, 4]),(pw3,6,[0, 1, 3, 4, 5]),(pw5,7,[0, 1, 2, 4, 5]),(pw9,7,[0, 1, 3, 2, 5]),(pw19,7,[1, 2, 3, 0, 4]),(pw17,5,[0, 2, 3, 4, 5]),(pw20,5,[1, 2, 3, 4])]
theorem p11_Y : ∀ s ∈ p11_Z, SliceN true p11_R p11_T s := by
  unfold p11_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p11_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p11_B p4_B p4_L (by decide +kernel),mkSlice (w:=0) p11_B p7_B p7_L (by decide +kernel),mkSlice (w:=0) p11_B p8_B p8_L (by decide +kernel),mkSlice (w:=0) p11_B p9_B p9_L (by decide +kernel),mkSlice (w:=0) p11_B p10_B p10_L (by decide +kernel),mkSlice (w:=32) p11_B p2_B p2_L (by decide +kernel),by simp⟩
def p11_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(2,[129]),(3,[129]),(6,[]),(2,[131]),(3,[131]),(4,[386]),(2,[257]),(3,[385]),(4,[389]),(2,[514]),(1,[514]),(3,[514]),(4,[129]),(2,[261]),(3,[389]),(2,[262]),(3,[390]),(4,[130]),(1,[517]),(2,[517]),(3,[517]),(2,[519]),(2,[260,21]),(4,[389,129]),(2,[514,149]),(2,[261,404]),(2,[261,406]),(4,[129,534])]
def p11_t : Tabs := (p11_C.map (mkCut true p11_Z),[(9,8),(3,2),(3,1),(37,36),(21,17),(9,1),(21,5),(18,2),(33,1),(6,4),(6,2),(10,2),(6,36),(12,4),(37,5),(9,17),(10,34),(33,17),(35,2),(7,5),(12,8),(20,4),(20,5),(10,8),(9,5),(49,17),(33,0),(37,4),(49,16),(25,24),(6,34),(33,5),(10,40),(3,5),(6,1),(18,17),(3,17),(19,1),(20,17),(7,2),(19,5),(38,2),(41,8),(19,17),(20,16),(25,17),(6,0),(18,0),(20,0),(50,34),(21,1),(18,32),(9,0),(10,0),(9,16),(10,32),(12,16),(12,32),(20,32),(20,1)],[],[[]])
theorem p11_W : TabsP true p11_R p11_T p11_t := ⟨cutsGood p11_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p11_D8 : List StD := [
([pw0,pw1,pw2,pw4,pw6,pw21],[0,4,8,12,16,1,17,3,21,25,33,5,13,29,9,37,41,45,49,53,57,61,65,69],[18593,4323,2341,8745,5297,98498,131332,8712,263313,524614,586,1049683,2097164,4194325,8388633])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p11_D7 : List StD := [
([pw0,pw1,pw22,pw2,pw4,pw6,pw21],[0,24,28,20,32,9,21,25,17,5,29,33,53,3,4,41,45,61,73,77,81,85],[41,8,8961,67,133,264705,1,557096,65642,1196,17,1073408,4162,2097284,2065,4418,1156,17,131078,19,21]),
([pw23,pw0,pw1,pw2,pw4,pw6,pw21],[20,32,36,40,44,41,29,45,24,1,9,13,4,37,53,61,77,85,89,3],[257,8193,528417,389,73,19,1027,2562,518,262154,2066,66561,133,73,19,16548,131176,50,32780,22,26]),
([pw0,pw1,pw2,pw24,pw4,pw6,pw21],[32,4,48,52,37,56,13,21,3,9,17,29,45,85,20,61,89,93,97],[849,3,2,197,65609,97,1810,147728,4244,10264,49,1,262150,1034,35,4228,10248,33,32780,133,41]),
([pw25,pw0,pw1,pw2,pw4,pw6],[32,60,21,68,33,73,64,29,81,85,3,5,9,37,41,45,53,57,61,101,105,109,113],[2049,5137,131089,7,524305,1048609,2097185,7,4194337,25920,32774,648,65542,968,262154]),
([pw0,pw1,pw2,pw10,pw4,pw6,pw21],[4,72,1,76,80,29,37,45,3,41,5,21,25,33,20,13,32,49,53,57,61,65,69,77,117,121],[8389700,33541,66820,3204,16781348,41222,16449,1,2248,4208,139586,16384,262665,4625,33554947,2184,304,532482,1048760,2097290,4194354]),
([pw11,pw0,pw1,pw2,pw4,pw6,pw21],[20,84,88,92,5,29,4,45,81,32,13,25,77,3,16,76,9,17,21,33,37,49,61,65,69,125],[8721,65537,32769,131,37,16897,1052673,132368,262290,2100,533528,4161,131,37,2097161,322,2084,33554760,4194310,8388618,16777228]),
([pw0,pw1,pw2,pw4,pw6,pw26],[32,5,20,96,100,104,49,1,41,85,29,45,53,129,108,13,57,61,81,117,3],[199,32771,131,524291,131,1057100,10324,1636,16385,6424,1832,327689,131120,4113,545])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p11_D6 : List StD := [
([pw1,pw22,pw2,pw24,pw4,pw6,pw21],[32,45,5,9,29,13,17,85,21,53,56,112,37,61,133,137,141,145,149,153],[4096,49160,65548,266,393224,9,524384,2084,546,176,1025,1,514,208,65,262,148,5,8210,3,17]),
([pw0,pw1,pw2,pw27,pw4,pw6,pw21],[21,29,33,37,5,41,9,45,3,8,12,16,32,1,49,61,65,69,73,81,85,89,93,97,125,149,153],[72,67108912,8192,145,2097170,262164,72,4194304,137,33554442,16396,524288,8388641,1048610,16777252,769,1282,6148,32771,65541,131078]),
([pw28,pw0,pw1,pw2,pw4,pw6,pw21],[13,53,85,37,57,5,21,29,9,33,41,45,49,61,65,69,89],[33,264,1024,66,132,528,33,33,67,65541,33,264,2058,140,4120,66,132,528,8198,16402,32788]),
([pw0,pw1,pw2,pw29,pw4,pw6,pw21],[29,37,13,33,45,41,1,9,21,12,5,49,53,57,61,65,69,81,85,89,121,149,157,3],[130,4194340,1092,68,524293,68,130,130,274,2097155,2058,131072,4144,262177,1048616,272,8389121,8200,16401,32792,65545]),
([pw0,pw1,pw24,pw10,pw4,pw6,pw21],[21,17,29,33,37,13,45,20,116,41,52,5,9,49,61,65,69,85,89,125,133,153,161,165],[1048592,2048,2097186,97,262180,288,656,4096,81,4194324,8216,642,65,131076,8388872,67,1026,524298,16389,32777,65548]),
([pw30,pw0,pw1,pw2,pw4,pw6,pw21],[5,45,29,33,41,13,17,21,85,16,32,9,61,65,69,89,93,97,125,129],[33,2048,80,130,260,1544,33,33,131,32773,33,80,130,260,589832,131090,80,262168,4102,8202,16396]),
([pw0,pw1,pw31,pw2,pw4,pw6],[32,105,21,81,120,9,29,41,85,5,33,53,45,57,77,101,109,113,169,173,177,181],[515,515,65539,262147,131075,1,16552,4148,524640,9352,2068,34112,2188,1048904,2097172]),
([pw25,pw0,pw1,pw2,pw10,pw4,pw6],[21,25,37,41,29,45,57,33,77,105,109,68,5,9,53,61,81,133,3],[4096,260,200,192,97,82,260,1544,1536,33,18,131084,8192,37,22,65536,16393,26,33,264194,32771]),
([pw25,pw11,pw0,pw1,pw2,pw4,pw6],[17,21,25,33,77,29,45,81,32,37,5,9,41,61,73,105,185,3],[131336,1024,536,137,74,44,49408,2048,4096,66,36,528,129,66,36,65553,82,52,129,129,8198]),
([pw32,pw0,pw1,pw2,pw4,pw6,pw21],[9,21,33,17,25,29,37,41,45,16,32,1,5,49,61,65,69,97,105,125],[4096,65,136,258,48,1540,65,136,258,48,264196,65,259,49,8197,131082,136,524300,16402,32774,65556]),
([pw0,pw1,pw2,pw10,pw4,pw6,pw26],[1,29,45,20,5,41,33,53,57,85,104,13,21,37,61,89,129,3],[17,2049,17,17,32771,17,40,65536,12,10,8192,8,164,514,352,4100,132098,320,16390,132,514]),
([pw33,pw0,pw1,pw2,pw10,pw4,pw21],[1,57,45,5,37,85,21,33,13,29,124,41,49,53,65,133,189,193],[9,560,544,1024,100,162,9,257,9,9,259,34832,65536,84,4114,131072,8196,130,68,130,16390]),
([pw33,pw0,pw1,pw2,pw4,pw21],[128,21,29,189,193,132,1,33,5,25,45,13,37,41,57,3,53,65,77,197,201,205],[836,4620,8724,1031,540804,262472,1050704,1283,35040,12312,1035,2130088,65555,16560,131107]),
([pw0,pw34,pw1,pw2,pw4,pw6,pw21],[25,33,37,17,21,5,9,29,45,81,16,32,1,41,49,53,61,65,69,73,85,125,157],[4096,68,4194344,304,161,524322,68,8712,32784,1048577,3074,68,276,133,16390,520,137,2097162,65553,131090,262147])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p11_D5 : List StD := [
([pw35,pw0,pw1,pw2,pw6,pw21],[29,33,41,209,9,21,5,37,61,65,69,73,97,149,153,213,217,221,225,229],[72,32816,4132,289,546,72,16396,65545,2058,148,8209,131090,262149,524294,1027]),
([pw36,pw0,pw1,pw2,pw4,pw21],[5,21,29,33,41,189,9,45,1,37,61,65,69,73,81,97,153,205,233],[261,100,16404,1030,4108,97,65553,131,8201,560,162,131112,32786,262168,2058]),
([pw37,pw0,pw1,pw2,pw4,pw21],[1,9,29,45,57,41,21,37,33,5,53,65,81,105,205,237],[517,134,4132,76,276,131,32801,73,8209,130,74,16402,1064,304,2072]),
([pw25,pw33,pw0,pw1,pw2,pw4],[29,45,21,25,37,41,201,77,5,53],[9,256,144,96,6,9,9,9,7,144,96,6,112,22,546]),
([pw38,pw0,pw1,pw2,pw4,pw6],[105,17,37,53,81,85,5,9,21,29,25,41,45,61],[65,132,2066,264,544,65,19,265,1057,132,4108,548,18,18,8232]),
([pw33,pw0,pw1,pw2,pw4,pw26],[1,5,45,85,21,29,41,193,37,53,237],[3,40,40,28,40,3,1089,3,3,192,20,256,516,192,20])]
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p11_C6x0 : levelOK true p11_T p11_t 5 (p11_D5.map Prod.fst) ((p11_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p11_I6 : LevelN true p11_T 6 p11_D6 := levelStep p11_B p11_W p11_I5 (chunks 32 p11_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p11_C6x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p11_C7x0 : levelOK true p11_T p11_t 6 (p11_D6.map Prod.fst) ((p11_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p11_I7 : LevelN true p11_T 7 p11_D7 := levelStep p11_B p11_W p11_I6 (chunks 32 p11_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p11_C7x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p11_C8x0 : levelOK true p11_T p11_t 7 (p11_D7.map Prod.fst) ((p11_D8.drop (0*32)).take 32) = true := by decide +kernel
theorem p11_I8 : LevelN true p11_T 8 p11_D8 := levelStep p11_B p11_W p11_I7 (chunks 32 p11_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p11_C8x0
  ))
theorem p11_L : LowN true p11_R p11_T 9 := lowSearch p11_B p11_I8 (by decide +kernel)
def p12_T : Nat := 0xeeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8eeeaeee8
def p12_R : List Nat := [0, 1, 2, 3, 4]
def p12_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,1,17)]
theorem p12_B : baseOK p12_T p12_R p12_E = true := by decide +kernel
def p12_Z : List SliceD := [(pw3,5,[0, 1, 3, 4])]
theorem p12_Y : ∀ s ∈ p12_Z, SliceN true p12_R p12_T s := by
  unfold p12_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p12_B p3_B p3_L (by decide +kernel),by simp⟩
def p12_C : List (Nat × List Nat) := [(0,[])]
def p12_t : Tabs := (p12_C.map (mkCut true p12_Z),[(5,4),(6,4),(3,2),(3,1),(6,2),(5,1),(10,2),(9,8),(9,1)],[],[[]])
theorem p12_W : TabsP true p12_R p12_T p12_t := ⟨cutsGood p12_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p12_D5 : List StD := [
([pw0,pw1,pw2,pw4,pw6],[0,1,5,17,25,9,13,21,33,29],[102,170,786,3,204,261,5,25,9,17])]
def p12_D4 : List StD := []
theorem p12_I4 : LevelN true p12_T 4 p12_D4 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p12_C5x0 : levelOK true p12_T p12_t 4 (p12_D4.map Prod.fst) ((p12_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p12_I5 : LevelN true p12_T 5 p12_D5 := levelStep p12_B p12_W p12_I4 (chunks 32 p12_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p12_C5x0
  ))
theorem p12_L : LowN true p12_R p12_T 6 := lowSearch p12_B p12_I5 (by decide +kernel)
def p13_T : Nat := 0xfffefeeefffefeeefffefeeefffefeeefffefeeefffefeeefffefeeefffefeee
def p13_R : List Nat := [0, 1, 2, 3, 4]
def p13_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,8,12),(3,4,12),(4,4,20)]
theorem p13_B : baseOK p13_T p13_R p13_E = true := by decide +kernel
def p13_Z : List SliceD := [(pw7,5,[1, 2, 3, 4])]
theorem p13_Y : ∀ s ∈ p13_Z, SliceN true p13_R p13_T s := by
  unfold p13_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p13_B p6_B p6_L (by decide +kernel),by simp⟩
def p13_C : List (Nat × List Nat) := [(0,[])]
def p13_t : Tabs := (p13_C.map (mkCut true p13_Z),[(1,0),(2,0)],[],[[]])
theorem p13_W : TabsP true p13_R p13_T p13_t := ⟨cutsGood p13_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p13_D5 : List StD := [
([pw0,pw1,pw2,pw4,pw6],[0,1,5],[7,3,3,3,5,5,5,1,1,1])]
def p13_D4 : List StD := []
theorem p13_I4 : LevelN true p13_T 4 p13_D4 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p13_C5x0 : levelOK true p13_T p13_t 4 (p13_D4.map Prod.fst) ((p13_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p13_I5 : LevelN true p13_T 5 p13_D5 := levelStep p13_B p13_W p13_I4 (chunks 32 p13_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p13_C5x0
  ))
theorem p13_L : LowN true p13_R p13_T 6 := lowSearch p13_B p13_I5 (by decide +kernel)
def p14_T : Nat := 0xfeeefac8feeefac8feeefac8feeefac8feeefac8feeefac8feeefac8feeefac8
def p14_R : List Nat := [0, 1, 2, 3, 4]
def p14_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,1,9),(4,1,17)]
theorem p14_B : baseOK p14_T p14_R p14_E = true := by decide +kernel
def p14_Z : List SliceD := [(pw3,5,[0, 1, 4, 3])]
theorem p14_Y : ∀ s ∈ p14_Z, SliceN true p14_R p14_T s := by
  unfold p14_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p14_B p3_B p3_L (by decide +kernel),by simp⟩
def p14_C : List (Nat × List Nat) := [(0,[])]
def p14_t : Tabs := (p14_C.map (mkCut true p14_Z),[(9,8),(6,4),(3,2),(3,1),(6,2),(21,20)],[],[[]])
theorem p14_W : TabsP true p14_R p14_T p14_t := ⟨cutsGood p14_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p14_D5 : List StD := [
([pw0,pw1,pw2,pw4,pw6],[0,1,5,17,9,13,21],[54,75,17,3,33,5,5,9,9,1])]
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
def p15_T : Nat := 0xeeeaeee0eeeaeee0eeeaeee0eeeaeee0eeeaeee0eeeaeee0eeeaeee0eeeaeee0
def p15_R : List Nat := [0, 1, 2, 3, 4]
def p15_E : List (Nat × Nat × Nat) := [(0,4,5),(1,4,6),(2,1,5),(3,1,9),(4,1,17)]
theorem p15_B : baseOK p15_T p15_R p15_E = true := by decide +kernel
def p15_Z : List SliceD := [(pw3,4,[0, 3, 1, 4])]
theorem p15_Y : ∀ s ∈ p15_Z, SliceN true p15_R p15_T s := by
  unfold p15_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p15_B p5_B p5_L (by decide +kernel),by simp⟩
def p15_C : List (Nat × List Nat) := [(0,[])]
def p15_t : Tabs := (p15_C.map (mkCut true p15_Z),[(5,4),(17,18),(6,4),(6,2),(5,0),(9,1),(9,0),(17,1),(17,0),(5,1),(9,3),(17,3)],[],[[]])
theorem p15_W : TabsP true p15_R p15_T p15_t := ⟨cutsGood p15_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p15_D4 : List StD := [
([pw0,pw1,pw2,pw4,pw6],[1,9,13,0,21,29,5,17,25,33,37,41,45],[67,133,273,545,1030,2066,4130,12,12,24])]
def p15_D3 : List StD := []
theorem p15_I3 : LevelN true p15_T 3 p15_D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p15_C4x0 : levelOK true p15_T p15_t 3 (p15_D3.map Prod.fst) ((p15_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p15_I4 : LevelN true p15_T 4 p15_D4 := levelStep p15_B p15_W p15_I3 (chunks 32 p15_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p15_C4x0
  ))
theorem p15_L : LowN true p15_R p15_T 5 := lowSearch p15_B p15_I4 (by decide +kernel)
def p16_T : Nat := 0xfefefeeefefafe88fefefeeefefafe88fefefeeefefafe88fefefeeefefafe88
def p16_R : List Nat := [0, 1, 2, 3, 4, 5]
def p16_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,8,12),(3,1,9),(4,1,17),(5,1,33)]
theorem p16_B : baseOK p16_T p16_R p16_E = true := by decide +kernel
def p16_Z : List SliceD := [(pw3,6,[0, 1, 3, 5, 4]),(pw2,6,[3, 4, 0, 1, 5]),(pw5,7,[4, 0, 1, 5, 2]),(pw9,7,[3, 1, 0, 5, 2]),(pw19,6,[0, 3, 2, 4, 1]),(pw7,5,[1, 2, 3, 4, 5]),(pw18,4,[2, 3, 1, 4]),(pw17,5,[0, 2, 3, 4, 5]),(pw39,5,[0, 1, 3, 4]),(pw40,4,[0, 4, 2, 5])]
theorem p16_Y : ∀ s ∈ p16_Z, SliceN true p16_R p16_T s := by
  unfold p16_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p16_B p12_B p12_L (by decide +kernel),mkSlice (w:=4) p16_B p13_B p13_L (by decide +kernel),mkSlice (w:=0) p16_B p7_B p7_L (by decide +kernel),mkSlice (w:=0) p16_B p8_B p8_L (by decide +kernel),mkSlice (w:=0) p16_B p14_B p14_L (by decide +kernel),mkSlice (w:=0) p16_B p10_B p10_L (by decide +kernel),mkSlice (w:=0) p16_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p16_B p15_B p15_L (by decide +kernel),mkSlice (w:=0) p16_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p16_B p5_B p5_L (by decide +kernel),by simp⟩
def p16_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(2,[262]),(5,[]),(2,[263]),(2,[260]),(3,[260]),(6,[]),(7,[]),(2,[261]),(3,[261]),(3,[263]),(3,[262]),(2,[517]),(3,[521]),(2,[519]),(3,[523]),(8,[]),(2,[389]),(3,[393]),(2,[388]),(2,[390]),(3,[394]),(2,[393]),(3,[389]),(2,[394]),(3,[390]),(9,[]),(2,[260,21]),(2,[260,405]),(2,[392,149]),(2,[388,277]),(2,[261,406]),(2,[261,404])]
def p16_t : Tabs := (p16_C.map (mkCut true p16_Z),[(9,8),(10,8),(3,2),(3,1),(12,8),(3,6),(9,1),(10,2),(17,1),(20,4),(34,2),(33,32),(33,1),(22,18),(22,6),(34,32),(44,40),(10,18),(44,36),(52,36),(17,18),(37,36),(38,36),(20,6),(12,4),(37,5),(12,36),(34,18),(7,6),(19,18),(7,5),(3,0),(33,36),(9,4),(17,4),(17,0),(41,40),(49,48),(9,40),(26,24),(26,18),(33,0),(34,0),(38,6),(17,16),(42,40),(50,48),(34,6),(50,18),(9,5),(33,5),(20,36),(20,16),(3,18),(19,2),(3,5),(7,1),(7,2),(33,2),(10,40),(12,0),(12,40),(44,8),(44,4),(52,4),(50,16),(9,0),(3,4),(3,32),(35,1),(37,1),(35,2),(33,4),(19,6)],[],[[]])
theorem p16_W : TabsP true p16_R p16_T p16_t := ⟨cutsGood p16_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p16_D8 : List StD := [
([pw0,pw1,pw2,pw4,pw6,pw21],[0,4,8,12,17,33,3,25,16,1,29,37,41,49,5,9,13,21,45,53,57,61,65,69,73,77],[115264,131667,1156,2088,274752,524307,1156,1048616,2109760,23,2107,4194323,8388620,16777348,33554472])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p16_D7 : List StD := [
([pw41,pw0,pw1,pw2,pw4,pw6,pw21],[24,32,36,40,44,1,3,20,5,33,85,89,0,4,16,28,25,37,49,69,81,93,97,101,105,109],[129,32769,12289,195,69,16457,1048593,1057,35,517,1065,2320,274,2097172,2072,4259842,131588,8650760,524294,16777226,33554444]),
([pw0,pw1,pw22,pw2,pw4,pw6,pw21],[24,44,48,52,9,13,25,33,49,3,53,29,41,57,97,0,4,16,17,37,65,69,73,77,81,101,113,117,121],[16777267,2,67109393,2133,134217873,4881,1,268436514,2150,8362,4898,361472,16452,524424,131840,16452,8328,34604288,2097164,4194372,8389000]),
([pw42,pw0,pw1,pw2,pw4,pw6,pw21],[24,20,40,44,56,25,33,49,32,9,57,0,4,48,5,29,41,53,69,89,97,101,105,109,113,125],[264,8193,6145,291,81,133,33554953,16777729,35,81,133,671752,32810,1112,65676,1048610,1104,2097284,262162,4194310,8388628]),
([pw23,pw0,pw1,pw2,pw4,pw6,pw21],[44,28,60,40,29,57,41,3,48,1,13,33,85,0,4,5,25,49,65,69,73,77,97,101,121,125],[257,32769,24577,275,37,201,33555465,4744,65554,2084,135744,16778241,19,37,201,4194322,2084,8650824,524294,1048594,2097188]),
([pw0,pw1,pw24,pw4,pw6,pw21],[40,64,68,4,25,33,129,41,17,21,49,53,3,0,13,29,57,61,65,69,73,77,133,137],[21057,8192,4194387,8388709,1729,2312,32786,65572,136321,282,2092,262281,524294,1048595,2097189]),
([pw43,pw0,pw1,pw4,pw6,pw21],[40,0,72,76,1,53,80,17,9,25,33,41,49,4,13,29,45,57,65,69,105,109,141,3],[8192,162,162,162,262178,8405265,789,4195353,71697,33284,132104,6209,524300,1048645,2097225]),
([pw0,pw1,pw2,pw4,pw6,pw21,pw44],[40,5,45,25,33,84,13,17,49,53,3,88,57,0,4,44,9,29,41,61,73,77,85,97,101,121,145,149,153,157,161],[1095,4194309,67108869,134217733,268435717,65537,33555074,131146,536875026,525571,33859,8389256,4752,16777473,24577,1073741880,1048609,41,2099201,2065,262145]),
([pw25,pw0,pw1,pw2,pw4,pw6,pw21],[40,96,100,13,25,33,41,45,3,92,57,0,4,44,17,29,49,53,69,85,97,105,109,121,165,169,173],[513,8457,6145,531,37,65537,393,524417,19,37,16777409,8536072,32794,1068,33554753,1048594,1060,67108929,262150,2097155,4194309]),
([pw0,pw1,pw2,pw4,pw6,pw21,pw26],[80,1,17,61,29,37,53,3,104,9,25,41,44,57,12,40,108,33,45,73,113,161,177,181,185,189,193],[650,1048711,1554,4325410,264323,33410,77,8389656,16785448,4105,1,69,69,33556485,69,2097456,524545,1296,67110913,90144,4096]),
([pw45,pw0,pw1,pw2,pw4,pw6,pw21],[80,40,44,116,1,112,53,3,9,57,29,49,21,25,33,41,61,69,105,165,197,201,205],[406,2,69,1060,524,32773,406,4307,8466,16922,526481,69,1060,524,65543,1048609,73,2099267,131112,262179,4194315])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p16_D6 : List StD := [
([pw0,pw1,pw2,pw46,pw6,pw21],[40,44,1,5,85,89,120,17,25,33,101,209,37,49,81,97,105,157,161,177,193],[16399,21,21,524293,21,42,42,131082,43,35200,6784,9217,262976,65601,1049601]),
([pw0,pw1,pw2,pw4,pw47,pw21],[40,1,5,17,25,33,41,53,213,124,57,85,89,29,49,97,101,105,157,161,193],[263,2051,259,259,2051,4236,12308,263204,16453,32920,1192,65601,524848,131585,1048641]),
([pw0,pw1,pw2,pw4,pw6,pw48],[40,44,1,5,85,89,128,17,25,33,101,209,37,49,81,97,105,157,161,177,193],[16399,21,21,524293,21,42,42,131082,43,35200,6784,9217,262976,65601,1049601]),
([pw0,pw1,pw22,pw24,pw4,pw6,pw21],[40,49,25,33,13,17,53,41,9,21,29,37,57,69,97,105,109,129,3],[17,131072,256,5,9,642,1,112,1044,4120,131,96,16388,2056,262147,100,104,131,8204,32771,65539]),
([pw43,pw0,pw1,pw22,pw4,pw6,pw21],[49,13,25,33,53,9,17,29,41,40,1,5,21,37,57,69,81,97,105,109,189,217,3],[4096,82,80,80,80,1048593,65570,1024,164,2097192,289,2048,134,16394,259,131076,8200,4194817,32780,262149,524297]),
([pw1,pw22,pw2,pw4,pw6,pw21,pw44],[29,57,13,17,9,33,49,25,45,53,132,5,21,37,41,69,73,77,81,97,153,201,221,225,3],[2048,12582916,133,38,16777284,262164,520,524289,8194,1048896,1296,521,34,2097224,4120,32771,65537,129,131074,34,16384]),
([pw25,pw1,pw22,pw2,pw4,pw6,pw21],[25,33,13,9,17,41,29,53,57,40,1,5,21,37,45,49,69,81,97,105,109,189,217,221,225,229,233,3],[131084,1024,33558536,73,4194314,32768,2048,25165828,69,262,201326596,144,262145,8194,16896,145,258,2097200,65539,524321,1048610]),
([pw0,pw22,pw2,pw4,pw6,pw21,pw26],[25,33,9,17,53,13,41,29,61,136,1,21,37,49,57,69,73,81,97,109,189,217,229,233,237,3],[1024,4196356,133,2097158,41943044,131108,24,262145,4098,16777536,800,25,26,1048648,56,32771,65537,129,524354,16386,8192]),
([pw45,pw0,pw22,pw2,pw4,pw6,pw21],[29,57,9,49,13,17,33,25,53,40,1,5,21,37,41,69,81,97,105,169,201,205,221,225,229,3],[65556,2048,12582928,145,82,16384,1024,16781316,133,70,33554444,288,131073,8194,524808,289,66,1048616,32771,262153,2097162]),
([pw0,pw1,pw49,pw22,pw2,pw4,pw6],[25,33,9,13,49,17,29,41,53,57,140,1,5,21,37,69,81,97,109,201,217,221,225,229,3],[65548,148,2048,8396804,69,1048582,152,4096,6291464,73,522,1024,524336,16777233,262162,288,131073,16386,289,514,32771]),
([pw0,pw1,pw2,pw4,pw6,pw21,pw50],[25,33,9,13,49,17,29,57,140,1,5,21,37,41,45,53,69,73,81,97,109,197,201,217,221,225,229,241],[262156,67110916,69,8388614,16404,512,50331656,73,138,8216,1024,136314881,130,4194352,32800,65539,131073,524289,1048594,4098,256]),
([pw51,pw0,pw1,pw2,pw4,pw6,pw21],[17,45,37,61,97,53,9,13,25,33,21,29,49,57,69,105,205,245,249,253,257],[66,136,33,272,516,4096,66,1027,274,518,66,41,2072,8204,136,33,33,393217,16404,557072,1114116]),
([pw51,pw0,pw1,pw22,pw2,pw4,pw6],[53,9,17,25,33,41,37,97,49,144,13,21,29,57,69,81,165,169],[290,288,512,37,168,112,33794,65536,2051,138,82,131072,5,4104,8208,5,136,80,5,5,16408]),
([pw51,pw0,pw1,pw2,pw4,pw6],[140,41,97,165,169,17,37,53,25,33,9,13,49,29,57,101,113,117,121,161,193,261,3],[5130,6162,32930,263,1049154,3096,4259880,269,131656,262320,8213,2113616,389,736,524293]),
([pw0,pw1,pw2,pw4,pw6,pw21,pw52],[1,13,17,29,33,41,57,25,45,61,49,53,69,73,109,125,129,141,189,221,241,265],[32771,65541,2097161,131089,257,257,524294,138,82,546,514,1048588,84,262180,2052,4120,8200,136,16432,80,1024]),
([pw23,pw0,pw1,pw24,pw4,pw6,pw21],[49,17,25,33,41,53,29,57,1,5,13,21,69,105,109,129,269],[2048,512,34,68,136,17,99328,256,68,136,17,34,68,136,17,34,34,19,4108,8197,16393]),
([pw23,pw43,pw0,pw1,pw4,pw6,pw21],[49,17,25,33,53,29,41,57,1,5,9,13,69,105,109,125,129,189],[18,1024,512,36,136,65,65536,18,18,18,131075,35072,36,136,65,36,136,65,4108,8197,16393]),
([pw23,pw0,pw2,pw4,pw6,pw21,pw26],[17,25,33,41,53,1,29,57,5,9,13,49,61,69,73,109,125,129,189,237,273],[512,17,66,132,528392,256,131105,66,132,1048616,66592,17,17,262153,17,8198,16386,66,32780,132,2048]),
([pw0,pw1,pw24,pw4,pw6,pw21,pw26],[25,33,21,61,40,17,53,29,41,57,129,9,49,69,73,109,133,137,189,3],[1036,2048,65541,131078,1028,524308,104,137,522,24,16,97,98,262416,96,8195,16385,129,33026,514,4096]),
([pw45,pw0,pw1,pw24,pw4,pw6,pw21],[17,25,33,129,49,53,21,29,57,9,13,41,61,69,105,169,205,249],[72,1024,33,130,260,2048,72,512,138,268,72,33,130,260,36880,33,33,131089,8198,16402,65556]),
([pw0,pw1,pw2,pw4,pw6,pw44,pw26],[17,25,33,45,29,37,41,53,49,57,128,9,13,61,69,129,153,189,237,273,3],[1572872,32777,26,44,2048,65800,129,18,516,270400,4096,131,37,131137,129,16390,18,18,36,516,1344]),
([pw0,pw1,pw31,pw2,pw4,pw6,pw21],[9,25,33,13,41,17,29,45,53,57,140,5,21,37,49,69,81,97,105,109,189,217,221,225,229,277],[65545,129,16781313,67,2097157,129,2048,12582920,74,524,33554456,288,131074,8196,17424,290,516,1048624,32774,262162,524308]),
([pw25,pw45,pw0,pw1,pw2,pw4,pw6],[17,25,33,41,49,169,29,37,53,165,57,140,9,13,69,277,281,285,289,3],[2072,4096,32816,65553,82,148,131592,8192,265,74,1036,524832,262657,66,132,289,98,1060,259,133,16390]),
([pw53,pw0,pw1,pw2,pw4,pw6,pw21],[13,17,25,33,49,53,29,57,61,41,1,9,69,73,109,201,3],[2048,257,34,68,136,528,257,66562,68,136,528,35,69,137,257,34,34,32786,4108,8196,16408]),
([pw0,pw54,pw1,pw2,pw4,pw6,pw21],[13,25,33,9,17,49,53,29,61,140,1,21,37,41,57,69,81,97,105,201,205,217,229,285],[1024,65545,4196360,138,2097164,8388648,257,80,131074,4100,8736,81,131,16389,257,82,84,524336,32774,262178,1048612])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p16_D5 : List StD := [
([pw51,pw0,pw1,pw24,pw4,pw6],[13,17,25,33,49,53,289,21,37,97,5,9,29,57,69],[192,1041,50,532,280,192,2048,580,328,35,4101,8201,34,34,16396]),
([pw51,pw43,pw0,pw1,pw4,pw6],[17,25,33,53,165,13,49,9,37,97,5,21,29,57,69],[9,144,1120,578,324,2048,9,9,9,144,530,276,4130,8228,16390]),
([pw22,pw2,pw4,pw6,pw44,pw26],[17,37,53,97,9,25,33,1,5,13,21,29,57,69,81,153,237],[5,40,66,65664,33024,5,5,1041,5,8202,40,2056,66,4098,16912]),
([pw25,pw45,pw22,pw2,pw4,pw6],[25,33,9,13,17,29,53,57,1,5,21,37,69,81,97,217,221,225,229],[8204,256,263172,37,32774,512,196616,41,138,80,16385,2050,81,130,4099]),
([pw0,pw1,pw22,pw2,pw55,pw6],[25,33,9,13,17,29,53,57,1,5,21,37,69,81,97,217,221,225,229],[8204,256,263172,37,32774,512,196616,41,138,80,16385,2050,81,130,4099]),
([pw53,pw1,pw24,pw4,pw6,pw21],[13,21,29,53,33,41,25,49,1,5,9,57,69,73,109,293],[515,1034,70,32786,162,265,69,2065,161,76,264,168,4116,8196,16432])]
def p16_D4 : List StD := []
theorem p16_I4 : LevelN true p16_T 4 p16_D4 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p16_C5x0 : levelOK true p16_T p16_t 4 (p16_D4.map Prod.fst) ((p16_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p16_I5 : LevelN true p16_T 5 p16_D5 := levelStep p16_B p16_W p16_I4 (chunks 32 p16_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p16_C5x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p16_C6x0 : levelOK true p16_T p16_t 5 (p16_D5.map Prod.fst) ((p16_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p16_I6 : LevelN true p16_T 6 p16_D6 := levelStep p16_B p16_W p16_I5 (chunks 32 p16_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p16_C6x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p16_C7x0 : levelOK true p16_T p16_t 6 (p16_D6.map Prod.fst) ((p16_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p16_I7 : LevelN true p16_T 7 p16_D7 := levelStep p16_B p16_W p16_I6 (chunks 32 p16_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p16_C7x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p16_C8x0 : levelOK true p16_T p16_t 7 (p16_D7.map Prod.fst) ((p16_D8.drop (0*32)).take 32) = true := by decide +kernel
theorem p16_I8 : LevelN true p16_T 8 p16_D8 := levelStep p16_B p16_W p16_I7 (chunks 32 p16_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p16_C8x0
  ))
theorem p16_L : LowN true p16_R p16_T 9 := lowSearch p16_B p16_I8 (by decide +kernel)
def p17_T : Nat := 0xfeeefac0feeefac0feeefac0feeefac0feeefac0feeefac0feeefac0feeefac0
def p17_R : List Nat := [0, 1, 2, 3, 4]
def p17_E : List (Nat × Nat × Nat) := [(0,8,9),(1,4,6),(2,2,6),(3,1,9),(4,1,17)]
theorem p17_B : baseOK p17_T p17_R p17_E = true := by decide +kernel
def p17_Z : List SliceD := [(pw7,4,[1, 2, 3, 4]),(pw17,4,[0, 3, 2, 4]),(pw3,4,[0, 4, 1, 3]),(pw5,4,[1, 4, 0, 2]),(pw9,4,[2, 3, 0, 1])]
theorem p17_Y : ∀ s ∈ p17_Z, SliceN true p17_R p17_T s := by
  unfold p17_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p17_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p17_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p17_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p17_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p17_B p5_B p5_L (by decide +kernel),by simp⟩
def p17_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[])]
def p17_t : Tabs := (p17_C.map (mkCut true p17_Z),[(9,8),(11,10),(7,5),(21,20),(7,3),(9,1),(17,1),(12,8),(26,24),(11,3),(18,2),(12,4),(28,24),(21,5),(28,20),(26,10),(6,5),(6,3),(6,2),(6,4),(9,3),(17,5),(18,10),(7,4),(18,16),(12,5),(17,16),(18,3),(17,3),(7,2),(9,0),(17,0),(12,10),(9,10),(11,8),(14,8),(9,5),(12,20),(17,20),(21,16),(18,24),(26,16),(12,24),(12,0),(7,1),(12,16),(6,0),(6,1),(7,0),(11,2),(18,0),(18,8),(9,2),(17,2),(17,4)],[],[[]])
theorem p17_W : TabsP true p17_R p17_T p17_t := ⟨cutsGood p17_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p17_D6 : List StD := [
([pw0,pw1,pw2,pw4,pw6],[3,0,4,8,12,16,1,9,17,13,21,29,33,5,25,37,41,45,49,53,57,61],[8391,843,1619,16995,2445,37013,69797,133401,786729,3146801])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p17_D5 : List StD := [
([pw0,pw1,pw22,pw2,pw4,pw6],[25,45,73,5,9,21,29,41,16,1,65,69,77,81,85,89,3],[1048,512,2060,42,137,4096,84,8210,145,68,34,65793,38,16389,32771]),
([pw0,pw1,pw2,pw24,pw4,pw6],[21,41,77,13,17,25,45,97,12,1,65,69,73,81,85,89,93,3],[66564,2072,512,73,42,132,132,8197,38,4096,81,16402,131329,34,32771]),
([pw0,pw1,pw2,pw4,pw56,pw6],[25,73,77,21,41,1,9,17,29,45,61,81,85,101,105],[68,130,8232,16384,49,262,2060,68,21,258,130,4099,512,1033,17]),
([pw0,pw1,pw2,pw4,pw6,pw57],[45,73,77,21,25,9,17,1,29,41,57,81,85,105,109,113],[36,66,9,24592,128,262,2053,32788,36,11,4114,66,1025,9,512]),
([pw0,pw1,pw2,pw10,pw4,pw6],[25,45,73,77,1,37,41,5,21,29,53,65,69,89,93,97,117,121,125,129],[18440,69636,144,131090,262161,524300,32768,42,73,512,38,1029,258,65,8195]),
([pw0,pw1,pw2,pw4,pw12,pw6],[1,73,25,105,29,33,37,41,8,21,69,77,81,85,89,133,137,3],[98305,1027,9,9,9,18,4192,2048,164,18,131330,8198,512,16452,132]),
([pw0,pw1,pw2,pw4,pw6,pw58],[1,45,73,29,5,37,41,25,49,69,77,89,97,105,113,121],[17,517,32771,8193,17,12,34,20544,1024,14,260,12,2114,34,128]),
([pw0,pw1,pw2,pw4,pw14,pw6],[77,1,13,29,53,25,33,45,21,65,73,93,97,105,141,145,149],[2561,6,6,8194,6,16393,65,4097,65,32904,1024,56,256,65680,48]),
([pw0,pw1,pw2,pw4,pw6,pw59],[45,77,1,21,53,97,105,4,25,49,65,73,81,85,93,121,149,153,157,3],[17410,393220,32773,68,68,34,4099,34,524418,9,8720,2048,65553,9,256]),
([pw0,pw1,pw2,pw4,pw6,pw60],[73,77,29,105,1,61,97,0,21,25,57,65,69,89,93,117,161,165,169,3],[18434,36865,24,24,524424,7,196610,66,66,5,262177,5,9248,256,512])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p17_D4 : List StD := [
([pw61,pw0,pw1,pw2,pw4],[73,125,5,9,25,29,21,45,69,77,81],[6,536,49,208,6,259,6,41,1096,33]),
([pw62,pw0,pw1,pw2,pw6],[21,25,77,121,41,173,45,65,69,81,177,181],[73,517,65,19,140,296,26,1060,22,2082]),
([pw16,pw0,pw1,pw4,pw6],[41,73,185,25,173,29,1,69,81,117,181,189,193,197],[642,38,34,11,6148,8272,9,276,13,1041]),
([pw63,pw0,pw2,pw4,pw6],[45,77,185,21,201,1,29,65,85,93,97,105,189,193,205],[642,70,11,1026,12292,9,2080,13,276,16401]),
([pw64,pw1,pw2,pw4,pw6],[1,29,77,73,121,125,45,89,105,137,209,213,217],[517,11,81,257,14,1044,2084,10,4130,176])]
def p17_D3 : List StD := []
theorem p17_I3 : LevelN true p17_T 3 p17_D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p17_C4x0 : levelOK true p17_T p17_t 3 (p17_D3.map Prod.fst) ((p17_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p17_I4 : LevelN true p17_T 4 p17_D4 := levelStep p17_B p17_W p17_I3 (chunks 32 p17_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p17_C4x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p17_C5x0 : levelOK true p17_T p17_t 4 (p17_D4.map Prod.fst) ((p17_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p17_I5 : LevelN true p17_T 5 p17_D5 := levelStep p17_B p17_W p17_I4 (chunks 32 p17_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p17_C5x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p17_C6x0 : levelOK true p17_T p17_t 5 (p17_D5.map Prod.fst) ((p17_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p17_I6 : LevelN true p17_T 6 p17_D6 := levelStep p17_B p17_W p17_I5 (chunks 32 p17_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p17_C6x0
  ))
theorem p17_L : LowN true p17_R p17_T 7 := lowSearch p17_B p17_I6 (by decide +kernel)
def p18_T : Nat := 0xfefefeeefefafec0fefefeeefefafec0fefefeeefefafec0fefefeeefefafec0
def p18_R : List Nat := [0, 1, 2, 3, 4, 5]
def p18_E : List (Nat × Nat × Nat) := [(0,8,9),(1,4,6),(2,2,6),(3,1,9),(4,1,17),(5,1,33)]
theorem p18_B : baseOK p18_T p18_R p18_E = true := by decide +kernel
def p18_Z : List SliceD := [(pw7,6,[1, 2, 3, 4, 5]),(pw5,7,[0, 1, 2, 4, 5]),(pw8,5,[1, 2, 3, 5]),(pw18,5,[2, 1, 3, 4]),(pw65,5,[3, 1, 2, 0]),(pw17,5,[0, 2, 3, 4, 5]),(pw9,6,[1, 3, 0, 5, 2]),(pw3,5,[0, 1, 3, 5, 4]),(pw66,4,[0, 3, 2, 5]),(pw39,4,[0, 3, 1, 4]),(pw40,4,[0, 4, 2, 5])]
theorem p18_Y : ∀ s ∈ p18_Z, SliceN true p18_R p18_T s := by
  unfold p18_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p18_B p4_B p4_L (by decide +kernel),mkSlice (w:=0) p18_B p17_B p17_L (by decide +kernel),mkSlice (w:=0) p18_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p18_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p18_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p18_B p15_B p15_L (by decide +kernel),mkSlice (w:=0) p18_B p14_B p14_L (by decide +kernel),mkSlice (w:=0) p18_B p15_B p15_L (by decide +kernel),mkSlice (w:=0) p18_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p18_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p18_B p5_B p5_L (by decide +kernel),by simp⟩
def p18_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(1,[129]),(6,[257]),(7,[]),(1,[131]),(1,[257]),(1,[259]),(1,[260]),(8,[]),(9,[]),(1,[261]),(1,[262]),(1,[263]),(1,[389]),(1,[390]),(1,[517]),(1,[518]),(1,[393]),(1,[394]),(1,[521]),(1,[522]),(1,[260,21]),(4,[389]),(1,[258,149]),(1,[129,532]),(1,[129,534]),(1,[258,151]),(1,[131,405]),(1,[130,277]),(1,[257,404]),(1,[257,406]),(1,[130,279]),(1,[259,533]),(10,[]),(1,[260,405]),(1,[260,533]),(1,[392,149]),(1,[516,277]),(1,[390,21]),(1,[522,21])]
def p18_t : Tabs := (p18_C.map (mkCut true p18_Z),[(9,8),(19,18),(7,5),(37,36),(7,3),(9,1),(17,1),(33,1),(10,8),(12,8),(10,2),(26,24),(19,3),(34,32),(34,2),(12,4),(20,16),(20,4),(44,40),(37,5),(26,18),(44,36),(52,36),(50,18),(6,3),(6,2),(10,18),(12,36),(34,18),(6,4),(17,3),(33,5),(17,18),(17,16),(20,18),(38,36),(22,18),(6,0),(50,48),(6,18),(17,0),(20,36),(42,40),(28,24),(52,48),(33,36),(33,0),(6,1),(6,5),(9,3),(33,3),(9,2),(33,2),(34,0),(7,4),(7,2),(9,5),(37,4),(50,16),(10,24),(19,2),(34,48),(7,1),(9,4),(17,4),(10,0),(20,0),(17,5),(52,32),(12,40),(20,48),(19,16),(9,0),(34,36),(33,32),(6,36),(34,4),(12,0),(37,32),(12,1),(33,4),(6,8),(7,18),(10,1),(17,2),(10,16),(12,16),(12,32),(20,32),(7,36),(20,1)],[],[[]])
theorem p18_W : TabsP true p18_R p18_T p18_t := ⟨cutsGood p18_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p18_D8 : List StD := [
([pw0,pw1,pw2,pw4,pw6,pw21],[3,0,4,1,21,8,25,12,5,29,9,13,17,16,33,37,41,45,49,53,57,61,65,69,73,77,81,85,89,93],[1291,6155,286,362,2698,54273,65556,393313,1573505,2097172,12583009,50332289,67108884,134217748,805314656])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p18_D7 : List StD := [
([pw0,pw1,pw22,pw2,pw4,pw6,pw21],[0,12,20,24,8,9,25,28,21,29,3,5,37,61,69,101,32,41,49,57,77,97,105,109,113],[37,4,2100225,265,2241,515,1,37924,131372,262260,524838,103424,8456,16592,1538,8456,16592,1049090,4194328,8388618,16777426]),
([pw23,pw0,pw1,pw2,pw4,pw6,pw21],[20,8,12,36,101,1,41,57,3,24,9,13,25,32,61,69,77,105,109,113,117,121],[513,1048577,8465,585,259,133,1027,2082,42,4102,2086,1297,73,2097155,133,16472,36882,65684,131082,262156,524294]),
([pw0,pw1,pw2,pw24,pw4,pw6,pw21],[0,8,12,32,40,117,17,13,21,25,29,3,33,41,57,20,9,49,61,69,77,105,109,113],[67745,73,8,401,643,1157,6248,38944,8496,131618,17444,1,262488,524874,1049676,8464,2562,17412,2097170,4194324,8388614]),
([pw43,pw0,pw1,pw2,pw4,pw6,pw21],[32,8,12,44,117,69,1,61,3,40,5,17,29,20,41,49,57,101,105,109,113,125],[513,8465,131073,649,35,261,1090,2051,74,1122,4102,2321,16536,32818,69652,137,35,2097157,262154,524300,1048582]),
([pw0,pw67,pw1,pw2,pw4,pw6,pw21],[20,32,1,3,48,52,56,37,57,69,13,33,41,12,8,21,25,29,101,105,109,113,117,121,125,129,133,137],[8205,33556493,1166,37892,67174916,132356,4194305,262146,25,16425,8265,134217731,2065,8390689,321,146,674,16777410,528944,1053008,2098016]),
([pw0,pw1,pw2,pw10,pw4,pw6,pw21],[1,41,57,69,60,101,117,3,5,21,25,29,8,20,32,13,12,9,17,49,61,77,81,85,89,93,137,141,145],[131393,294945,4481,771,1289,34821,67133536,16384,594,524488,134219844,8192,1048626,268436520,2097316,530,5256,67716,4194330,8388630,50331660]),
([pw11,pw0,pw1,pw2,pw4,pw6,pw21],[20,52,64,1,41,49,9,57,3,12,5,13,37,69,32,60,21,29,33,61,73,77,85,89,105,117,141,149],[1801,262145,32769,21,35,897,33554505,6408,66580,8234,133256,134234177,21,35,67108929,524308,8226,3149952,16777222,4194324,8388642]),
([pw68,pw0,pw1,pw2,pw4,pw6,pw21],[32,56,68,52,61,69,77,13,3,5,17,33,57,12,60,21,25,37,41,45,49,81,93,101,109,145,149],[8577,16385,131073,21,297,67,2944,8389633,32916,66208,4162,67109897,262164,1574944,4170,21,33554473,67,2097172,16777222,4194410]),
([pw0,pw1,pw2,pw4,pw6,pw58,pw21],[8,52,1,45,5,37,72,101,3,16,13,21,29,49,153,56,25,41,57,61,73,77,85,105,113,157],[29,1029,21,21,21,1029,426,16394,11,1,16394,526496,33562881,33186,3149856,8388673,131138,4200512,65538,16785921,262658]),
([pw69,pw0,pw1,pw2,pw4,pw6,pw21],[8,20,16,76,101,25,41,57,3,1,13,45,56,49,61,69,77,81,109,129,161,165],[259,3,4370,74,8195,134,524291,1537,521,1048613,1029,2322,74,2051,134,16472,32801,65684,131081,262156,2097189]),
([pw0,pw1,pw2,pw4,pw6,pw21,pw26],[12,1,53,5,21,25,37,80,101,20,13,41,49,57,3,16,56,61,65,69,73,81,85,93,141,153,169],[15,1027,11,11,1027,11,16777540,67110932,33558564,517,1,131408,786528,1073153,82240,2097328,4194433,2192,8396801,36896,512]),
([pw45,pw0,pw1,pw2,pw4,pw6,pw21],[12,20,16,84,5,56,101,41,49,13,77,141,21,29,57,61,69,105,109,165,3],[19,3,1048674,138,262,16387,19,529,4105,21,529,2146,138,262,2051,33000,65892,9217,131084,262153,525317]),
([pw0,pw1,pw2,pw4,pw6,pw59,pw21],[8,1,117,65,5,21,29,56,88,33,13,61,69,77,3,16,20,9,41,45,53,57,81,85,89,145,173,177],[131094,1035,19,19,19,1027,33554956,262692,544773,82436,3145796,67110952,137,1,134225992,4194561,2336,8388960,128,16781313,41152]),
([pw70,pw0,pw1,pw2,pw4,pw6,pw21],[56,8,92,13,29,61,5,77,117,145,20,21,25,41,49,57,65,69,105,109,113,3],[11,2098433,3,37,131075,145,74,11,2054,74,11,66049,8484,20482,32785,37,515,145,262150,524293,1048579]),
([pw0,pw1,pw2,pw4,pw6,pw21,pw71],[12,56,1,117,73,96,5,13,33,3,16,21,25,77,177,20,9,29,41,45,49,53,61,69,81,109,165],[65612,149,69,69,133,133,794,264456,1576968,2105865,33546,16402,16402,19,1,16783392,33554465,4194338,67118081,8389634,131074]),
([pw72,pw0,pw1,pw2,pw4,pw6,pw21],[56,12,16,100,117,29,61,69,3,1,5,73,20,41,49,57,77,85,105,113,181,185],[259,4369,3,73,133,65537,1538,1048579,522,1030,2097187,2321,8280,16532,32801,73,133,2051,262156,131081,524325])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p18_D6 : List StD := [
([pw1,pw22,pw2,pw24,pw4,pw6,pw21],[21,29,5,13,25,97,193,61,69,56,104,108,41,57,101,105,109,113,117,121,125,129,181,189,197,201,3],[262144,75497504,2097220,16777281,524368,33554498,4194344,1036,137,280,522,16384,161,304,1048610,4101,2052,8198,32785,65539,131090]),
([pw0,pw67,pw22,pw2,pw4,pw6,pw21],[21,29,69,37,129,3,9,25,12,33,61,1,101,105,109,113,117,125,137,193,205,209,213],[524608,2048,56,1048593,148,2097170,65536,4096,97,100,290,262664,1025,132,4194818,1033,140,131082,8197,16387,32774]),
([pw68,pw0,pw22,pw2,pw4,pw6,pw21],[61,69,77,9,129,21,25,29,33,101,112,1,37,105,109,113,117,149,189,193,209,213],[524312,66568,4096,41,74,140,2048,262672,49,82,1048596,131840,33,66,2097412,33,66,132,8195,16389,32774]),
([pw0,pw1,pw2,pw27,pw4,pw6,pw21],[29,41,69,101,117,3,16,21,25,57,4,1,5,33,37,97,105,109,113,121,125,137,193,217,221,225],[12582928,16809992,2048,130,260,4609,2097176,8192,146,524308,529,16384,33554442,268,1048585,1058,100,97,65542,131075,262149]),
([pw28,pw0,pw1,pw2,pw4,pw6,pw21],[13,21,5,69,77,117,61,112,25,29,33,37,101,105,109,113,121,149,197,201],[5,1184,4096,194,264,528,5,5,67,5,5,133152,262178,65576,524336,66,264,528,8202,16402,32792]),
([pw51,pw0,pw1,pw22,pw2,pw4,pw6],[25,101,5,21,57,37,69,9,61,29,116,97,105,121,185,193,197,213],[532,528,1024,50,280,81,32900,16384,2054,268,69,131072,34,65672,8321,34,264,65,34,67,4105]),
([pw51,pw0,pw1,pw2,pw4,pw6],[120,57,61,185,213,37,69,5,9,21,25,101,29,17,41,49,65,77,81,93,229,233],[4234,4370,133154,519,525378,408,1056808,525,1224,2352,16405,2130000,2565,66656,262149]),
([pw0,pw1,pw2,pw29,pw4,pw6,pw21],[25,117,13,21,29,101,1,124,61,77,17,33,69,105,109,113,121,137,157,161,193,197,201,217,221],[9437186,16777252,68,68,524293,68,131106,2178,2097162,65539,4194322,1024,296,262177,560,392,4097,528,8201,16408,32785]),
([pw0,pw1,pw2,pw4,pw73,pw21],[1,41,57,69,101,237,9,21,29,241,128,13,17,25,37,49,61,73,77,85,89,245],[609,6161,643,8713,2309,16496,226,32872,2097444,81938,12312,393236,1162,525318,1048844]),
([pw68,pw23,pw0,pw2,pw4,pw6,pw21],[61,69,77,13,9,21,25,29,57,101,249,33,37,41,105,109,113,117,129,217,237],[131072,524312,4096,49,82,148,262144,1536,8193,1050626,260,1544,41,74,268,33,66,132,16387,32773,65542]),
([pw0,pw67,pw1,pw24,pw4,pw6,pw21],[21,25,57,33,181,3,17,29,12,37,1,41,97,101,105,109,113,117,121,137,253,257,261,265],[4416,56,1024,1048593,2097170,148,131072,8192,97,98,292,524808,4194313,262154,140,2049,8389122,132,16387,32773,65542]),
([pw11,pw0,pw1,pw24,pw4,pw6,pw21],[41,49,57,17,181,21,29,25,37,117,132,1,33,97,101,105,109,113,149,189,257,265],[8216,4096,17416,41,138,76,524816,2048,49,1048594,84,262912,33,130,68,33,2097410,68,32771,65541,131078]),
([pw30,pw0,pw1,pw2,pw4,pw6,pw21],[5,21,13,49,57,101,41,132,25,29,33,37,105,109,113,117,125,149,225,269],[5,32768,2208,194,264,528,5,5,67,5,5,132128,66,264,528,262178,524328,65584,4106,8210,16408]),
([pw74,pw0,pw1,pw2,pw24,pw4,pw21],[29,117,21,69,33,57,17,41,25,136,13,97,109,125,161,193,217,225,265],[264,26,264,512,140,41,98306,3136,16384,132,33,18,18,18,35,262144,131140,8257,132,33,4101]),
([pw74,pw0,pw1,pw2,pw4,pw21],[140,41,69,161,265,33,57,13,17,21,29,117,25,9,49,53,61,77,85,89,241,273],[4236,18468,4372,519,525380,1056808,408,523,1224,2352,2563,33888,65555,2228304,262147]),
([pw0,pw1,pw75,pw2,pw4,pw6,pw21],[5,29,101,41,49,117,1,21,25,57,144,9,37,97,105,109,113,125,137,185,217,225,269],[1048609,65,8197,65,65,524291,2048,262180,168,304,546,5124,136,272,514,2097164,4194324,131078,16408,32778,65554]),
([pw0,pw1,pw2,pw4,pw6,pw76],[1,41,57,69,117,277,17,5,25,148,9,21,29,33,61,229,45,49,77,81,93,281],[1169,32865,2179,393,36869,8304,10258,196632,5140,16482,2097448,262244,524810,16902,1048844]),
([pw11,pw43,pw0,pw1,pw4,pw6,pw21],[41,49,57,5,17,21,29,25,69,117,249,33,37,61,101,105,109,113,181,221,277],[16384,524312,2048,49,146,84,262144,1536,8193,258,1052676,1544,41,266,76,33,130,68,32771,65541,131078]),
([pw0,pw1,pw77,pw2,pw4,pw6,pw21],[33,57,69,37,9,41,17,25,29,21,1,97,105,109,113,121,125,193],[131089,1024,2120,544,132,258,17,17,17,32773,259,72,544,132,258,72,140,65546,4132,8226,16390]),
([pw1,pw77,pw2,pw4,pw6,pw21],[1,21,25,29,33,37,5,97,193,104,13,41,57,69,45,49,53,61,65,73,77,81,85,89,93],[337,432,2322,49172,69656,1185,2115,8261,5129,131234,270372,1572904,2097670,4194826,25165836]),
([pw0,pw1,pw2,pw78,pw6,pw21],[56,20,1,33,37,5,29,152,41,57,65,69,3,13,21,25,45,53,81,93,109,125,137],[4142,12309,16676,34852,581,4194315,131082,65546,523,1041,1041,2097233,264576,1048705,524353]),
([pw0,pw1,pw2,pw4,pw79,pw21],[56,20,1,33,37,5,29,157,156,41,57,69,3,13,21,25,45,53,81,93,109,125],[4142,12309,16932,34852,1093,139,131082,65546,1035,145,145,2097233,264960,1048833,524353]),
([pw0,pw1,pw2,pw4,pw6,pw80],[56,20,1,33,37,5,29,160,41,57,65,69,3,13,21,25,45,53,81,93,109,125,137],[4142,12309,16676,34852,581,4194315,131082,65546,523,1041,1041,2097233,264576,1048705,524353]),
([pw32,pw0,pw1,pw2,pw4,pw6,pw21],[9,17,21,25,29,41,57,69,101,117,5,105,109,113,121,125,137,225],[1024,513,258,36,136,80,513,258,36,136,80,65539,37,16393,81,131078,138,32786,2060,4116,8216]),
([pw0,pw2,pw10,pw4,pw6,pw58,pw21],[29,41,1,101,49,45,61,77,117,133,164,21,25,37,57,97,105,109,113,121,129,157,185,221,285,289,293],[8421384,17825796,33554438,516,516,4194309,8192,74,2097176,67109128,137,2050,524336,1312,129,65554,66,131075,4096,262161,16385]),
([pw69,pw0,pw2,pw10,pw4,pw6,pw21],[41,57,137,117,21,25,29,1,101,33,37,49,61,69,77,81,97,109,129,161,165,193,217,221,285],[6291464,268,512,25,2048,74,8454148,17039488,17,524448,66,1024,4101,260,16390,17,8224,66,32769,131075,1048610]),
([pw0,pw1,pw10,pw4,pw6,pw21,pw71],[1,41,49,117,5,77,101,21,25,73,297,168,29,33,61,105,109,125,137,157,165,193,217,301,305],[6291464,17,17,17,1025,1025,8192,138,268,25165832,262216,130,260,131616,2624,32774,65570,16386,1048612,524356,4096]),
([pw72,pw0,pw1,pw10,pw4,pw6,pw21],[25,61,117,29,101,1,21,5,49,57,33,37,41,77,85,97,105,113,137,157,185,193,217,221],[8421392,262164,2048,82,524305,8192,6291460,160,66,161,1048616,1024,4102,261,524,66,257,520,65539,16386,131081]),
([pw0,pw1,pw2,pw4,pw6,pw81,pw21],[29,41,101,117,1,21,69,57,65,133,25,33,37,61,77,97,105,109,113,121,185,193,217,221],[6291464,8421380,34,528,528,1048593,268,42,524360,2048,137,8198,260,4096,16389,65602,34,131075,1024,262209,129]),
([pw33,pw0,pw1,pw2,pw4,pw6,pw21],[1,45,29,13,21,65,117,57,101,25,41,49,61,77,81,93,109,161,193],[9,66,288,1040,2048,132,262147,9,9,131585,9,66,66,66,134,4144,288,8228,16400,65556,32772]),
([pw0,pw1,pw2,pw4,pw6,pw21,pw82],[25,41,101,117,1,21,57,49,297,29,33,37,53,61,97,105,109,113,125,137,157,161,193,201,217,221],[20971528,33570820,34,2097169,272,272,524300,42,137,8392712,1024,8198,1048581,262212,2048,32771,65602,34,131137,129,512]),
([pw83,pw0,pw1,pw2,pw4,pw6,pw21],[1,25,53,73,5,21,101,117,41,49,29,57,85,89,97,105,157,185],[17,132,72,288,514,2048,17,16393,17,17,132097,132,292,518,132,72,65546,72,32802,4128,8194]),
([pw0,pw34,pw1,pw2,pw4,pw6,pw21],[29,37,69,117,41,17,25,9,21,57,56,1,5,61,105,109,113,121,125,3],[2048,136,34,272,68,4609,136,34,8208,68,525313,42,280,131084,521,34,70,262147,16404,32785,65541]),
([pw0,pw1,pw2,pw4,pw6,pw21,pw84],[25,37,41,117,1,21,49,53,73,297,29,57,85,105,113,149,161,181,193,201,217,269,289,309],[1310728,131090,4194324,65553,528,528,32778,44,73,524424,136,8388614,2097155,258,258,8197,4100,36,18433,65,1024]),
([pw0,pw85,pw1,pw2,pw4,pw6,pw21],[33,57,69,41,101,9,29,17,21,25,16,1,105,109,113,121,125,225,3],[2048,33,144,264,516,66,33,144,264,263172,66,33,33,32773,67,131096,532,65554,4108,8202,16390]),
([pw0,pw1,pw2,pw4,pw6,pw86,pw21],[1,29,33,41,101,45,61,65,77,133,21,25,69,81,97,109,129,149,165,185,201,269,289],[65541,16401,4194313,513,513,524291,131092,1036,36,36,1048582,88,2097296,144,274,8200,72,32778,2048,266242,258]),
([pw0,pw1,pw2,pw4,pw58,pw59,pw21],[1,21,57,13,65,49,29,41,45,61,69,77,156,101,109,117,121,129,133,157,269,285],[2228225,9,9,262145,9,9,524304,130,32768,65824,324,530,1049616,8192,2068,130,514,16390,5152,68,2084]),
([pw87,pw1,pw2,pw4,pw6,pw21],[1,37,45,61,69,93,193,5,29,101,172,13,21,25,41,65,73,77,81,85,89,153,241],[197,2563,4233,8337,2337,582,16460,4194388,2097444,4618,40978,196642,263192,525352,1048880]),
([pw0,pw1,pw2,pw88,pw4,pw6,pw21],[117,25,57,1,45,61,101,13,21,29,69,37,77,81,97,109,161,165,193,217,221],[786433,1065024,136,136,65546,136,17,17,17,17,517,2048,352,1090,4164,288,1026,516,8226,32804,131078]),
([pw0,pw1,pw2,pw4,pw6,pw26,pw71],[1,41,49,5,53,21,25,57,61,69,77,160,73,101,105,117,125,181,201,297,301,313],[9,2228225,9,9,9,524289,1048592,50,84,32768,262288,258,516,70656,8192,16390,34,258,68,516,3200]),
([pw89,pw0,pw1,pw2,pw4,pw6,pw21],[1,21,25,77,117,5,53,57,41,49,13,37,101,105,109,113,225,269,309],[33,80,4096,258,516,136,33,1025,33,33,137,80,274,532,80,327682,133124,136,8198,16394,32780]),
([pw0,pw1,pw2,pw90,pw4,pw6,pw21],[117,29,41,49,101,1,5,21,25,53,77,37,61,97,105,109,137,157,165,185,193,217,221],[3145729,4202512,96,96,96,524322,65553,513,133,265,513,2048,4116,131096,1042,132,264,1026,16396,32774,262154]),
([pw63,pw0,pw1,pw2,pw4,pw6,pw21],[1,29,101,21,49,65,133,61,69,77,5,33,97,105,109,113,117,185,197,201,261],[65,65536,36,136,272,514,1025,4101,65,65,131075,36,1310728,272,526338,140,36,518,8216,16394,32786]),
([pw0,pw1,pw91,pw2,pw4,pw6,pw21],[29,101,1,41,117,49,5,65,21,25,57,33,61,77,97,105,109,113,185,193,217],[1572880,68,16390,68,68,262149,2048,146,280,560,1041,130,264,544,1025,4106,130,8195,32808,65545,131105]),
([pw92,pw1,pw2,pw4,pw6,pw21],[1,33,41,57,73,89,97,5,25,117,176,13,21,29,45,49,53,61,81,85,93,177,229],[643,2129,4229,417,10249,594,4614,49186,73738,131156,2097456,4194392,263204,525324,1048872]),
([pw0,pw1,pw93,pw2,pw4,pw6,pw21],[101,1,29,49,117,41,5,73,21,25,57,33,85,97,105,113,137,157,185,193,217],[1572880,66,8195,66,66,262150,2048,65553,304,536,1044,129,288,520,1028,129,131081,129,16424,4132,32780])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p18_D5 : List StD := [
([pw67,pw22,pw24,pw4,pw6,pw21],[21,25,29,33,129,189,3,1,37,101,105,109,113,117,205,209,257,317,321],[8192,512,97,98,100,152,131081,65546,262156,16401,274,32788,1027,2053,4102]),
([pw0,pw22,pw2,pw78,pw6,pw21],[29,37,69,61,129,25,1,9,21,33,105,109,113,125,137,193,205,209,213,325,3],[64,1048594,98320,52,131089,540674,136,36,262657,266,38,8195,1036,2057,4101]),
([pw0,pw22,pw2,pw4,pw79,pw21],[29,37,9,61,157,33,1,21,105,109,113,117,125,129,193,205,209,213,329,333,337,3],[64,2359298,557056,1064960,73729,18,136,2084,131105,18,18,4099,268,521,1029]),
([pw0,pw22,pw2,pw4,pw6,pw80],[21,37,69,9,129,25,33,61,1,101,105,109,113,117,137,193,205,209,3],[256,262162,65553,52,163856,16450,129,36,8264,131,38,522,1029,2057,4108]),
([pw35,pw0,pw1,pw2,pw6,pw21],[21,25,29,101,289,117,41,57,97,105,109,113,193,225,241,261,341,345,349],[81,65,8201,515,1029,4144,280,16402,148,32808,65570,132,131082,262156,2054]),
([pw36,pw0,pw1,pw2,pw4,pw21],[21,25,29,101,117,161,41,57,1,33,37,97,105,109,113,193,225,265,353],[290,530,1034,4099,16390,32816,2088,97,164,131096,81,148,65545,262156,8197]),
([pw94,pw0,pw1,pw2,pw4,pw6],[21,101,185,25,29,117,5,41,33,37,97,105,109,113,121,137,225,269],[68,304,530,4113,8216,68,1030,133,68,32802,161,16424,65539,131082,2057]),
([pw0,pw1,pw24,pw78,pw6,pw21],[25,33,57,21,181,29,1,37,41,97,105,109,113,117,121,137,253,257,265,325,3],[1048594,64,66064,131089,52,557058,8202,16387,38,264,262273,36,1033,2060,4101]),
([pw0,pw1,pw24,pw4,pw79,pw21],[21,33,57,181,17,29,37,157,1,97,105,109,113,117,253,257,261,3],[131082,256,16393,33288,44,194,65539,8210,38,193,192,36,1041,2053,4116]),
([pw0,pw1,pw24,pw4,pw6,pw80],[33,41,17,25,21,37,1,97,101,105,109,113,117,121,137,257,265,321,357,361,3],[1310721,64,18,557056,131200,16417,19,8201,4101,18,65576,292,522,1030,2060]),
([pw95,pw0,pw1,pw2,pw4,pw6],[37,185,17,61,69,117,5,21,25,9,101,105,121,197],[66,544,1029,136,272,66,7,138,66,37,8232,4144,5,273,2072]),
([pw96,pw0,pw1,pw2,pw4,pw21],[17,21,25,29,33,161,41,57,9,101,1,109,117,225,353],[1060,4116,517,70,140,304,545,98,168,273,82,152,8195,16393,2058])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p18_D4 : List StD := [
([pw22,pw24,pw78,pw6,pw21],[29,33,129,189,25,37,101,105,109,113,209,257,317,321,325],[16390,4106,2066,8195,76,36,1029,152,265,529]),
([pw22,pw24,pw4,pw79,pw21],[21,29,33,157,189,1,37,105,109,113,117,205,209,317,321],[44,8197,1044,16390,2057,72,4106,145,259,530]),
([pw22,pw24,pw4,pw6,pw80],[21,33,129,189,25,1,37,101,105,109,113,117,205,257,317],[38,16387,8210,2058,4101,68,140,273,521,1048])]
def p18_D3 : List StD := []
theorem p18_I3 : LevelN true p18_T 3 p18_D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p18_C4x0 : levelOK true p18_T p18_t 3 (p18_D3.map Prod.fst) ((p18_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p18_I4 : LevelN true p18_T 4 p18_D4 := levelStep p18_B p18_W p18_I3 (chunks 32 p18_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p18_C4x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p18_C5x0 : levelOK true p18_T p18_t 4 (p18_D4.map Prod.fst) ((p18_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p18_I5 : LevelN true p18_T 5 p18_D5 := levelStep p18_B p18_W p18_I4 (chunks 32 p18_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p18_C5x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p18_C6x0 : levelOK true p18_T p18_t 5 (p18_D5.map Prod.fst) ((p18_D6.drop (0*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p18_C6x1 : levelOK true p18_T p18_t 5 (p18_D5.map Prod.fst) ((p18_D6.drop (1*32)).take 32) = true := by decide +kernel
theorem p18_I6 : LevelN true p18_T 6 p18_D6 := levelStep p18_B p18_W p18_I5 (chunks 32 p18_D6 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p18_C6x0
  · exact p18_C6x1
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p18_C7x0 : levelOK true p18_T p18_t 6 (p18_D6.map Prod.fst) ((p18_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p18_I7 : LevelN true p18_T 7 p18_D7 := levelStep p18_B p18_W p18_I6 (chunks 32 p18_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p18_C7x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p18_C8x0 : levelOK true p18_T p18_t 7 (p18_D7.map Prod.fst) ((p18_D8.drop (0*32)).take 32) = true := by decide +kernel
theorem p18_I8 : LevelN true p18_T 8 p18_D8 := levelStep p18_B p18_W p18_I7 (chunks 32 p18_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p18_C8x0
  ))
theorem p18_L : LowN true p18_R p18_T 9 := lowSearch p18_B p18_I8 (by decide +kernel)
def p19_T : Nat := 0xfefefeeefefafc88fefefeeefefafc88fefefeeefefafc88fefefeeefefafc88
def p19_R : List Nat := [0, 1, 2, 3, 4, 5]
def p19_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,8,12),(3,2,10),(4,1,17),(5,1,33)]
theorem p19_B : baseOK p19_T p19_R p19_E = true := by decide +kernel
def p19_Z : List SliceD := [(pw3,6,[0, 1, 5, 3, 4]),(pw2,6,[3, 4, 0, 1, 5]),(pw5,7,[4, 0, 1, 5, 2]),(pw9,7,[3, 1, 0, 5, 2]),(pw19,7,[0, 2, 3, 1, 4]),(pw7,5,[1, 2, 3, 4, 5]),(pw17,5,[0, 2, 4, 3, 5])]
theorem p19_Y : ∀ s ∈ p19_Z, SliceN true p19_R p19_T s := by
  unfold p19_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p19_B p4_B p4_L (by decide +kernel),mkSlice (w:=4) p19_B p13_B p13_L (by decide +kernel),mkSlice (w:=0) p19_B p7_B p7_L (by decide +kernel),mkSlice (w:=0) p19_B p7_B p7_L (by decide +kernel),mkSlice (w:=0) p19_B p17_B p17_L (by decide +kernel),mkSlice (w:=0) p19_B p10_B p10_L (by decide +kernel),mkSlice (w:=0) p19_B p10_B p10_L (by decide +kernel),by simp⟩
def p19_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(2,[262]),(5,[]),(2,[263]),(2,[260]),(3,[260]),(4,[384]),(6,[]),(2,[261]),(4,[385]),(3,[261]),(3,[263]),(4,[386]),(3,[262]),(4,[387]),(2,[261,404])]
def p19_t : Tabs := (p19_C.map (mkCut true p19_Z),[(17,16),(10,8),(3,2),(3,1),(12,8),(13,9),(13,5),(10,2),(17,1),(20,4),(33,1),(34,2),(22,18),(22,6),(33,5),(17,9),(33,9),(34,18),(10,9),(37,36),(12,5),(38,36),(20,6),(12,4),(37,5),(7,6),(19,18),(7,5),(3,0),(3,9),(25,24),(26,24),(20,16),(44,40),(26,18),(25,9),(44,36),(41,9),(52,36),(50,18),(3,18),(33,0),(34,0),(3,5),(41,8),(11,9),(50,16)],[],[[]])
theorem p19_W : TabsP true p19_R p19_T p19_t := ⟨cutsGood p19_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p19_D8 : List StD := [
([pw0,pw1,pw2,pw4,pw6,pw21],[0,4,8,12,16,17,33,41,25,29,37,45,1,5,9,13,21,49,53,57,61,65,69,3],[8450048,65571,772,1096,2192,131107,772,262216,2192,39,1131,524467,1048588,2097172,4194328])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p19_D7 : List StD := [
([pw41,pw0,pw1,pw2,pw4,pw6,pw21],[24,32,36,40,44,3,20,1,5,77,85,0,4,28,29,33,37,41,61,65,69,73,81,89,93,97],[65,8193,6145,99,37,41,2097169,641,4194307,133,521,1296,274,8388628,1048,16793602,98308,33685512,262150,524298,1048588]),
([pw0,pw1,pw22,pw2,pw4,pw6,pw21],[24,44,48,52,9,13,33,56,21,25,41,29,45,49,53,0,4,17,37,61,65,69,73,93,97,101,105,109,3],[4194355,2,33554705,2581,67108945,5145,1,134225954,2598,16610,5162,229632,8389124,262336,268436488,2564,24896,16778504,524420,1048588,2097352]),
([pw42,pw0,pw1,pw2,pw4,pw6,pw21],[24,20,44,60,64,25,33,41,32,9,29,53,0,4,48,5,45,49,61,65,69,85,97,101,113],[260,16385,12289,291,73,145,16777733,8389121,35,73,145,2260996,1062,2124,65684,1058,2120,4194448,262154,524306,1048600]),
([pw23,pw0,pw1,pw2,pw4,pw6,pw21],[44,28,68,72,29,45,53,24,48,13,25,33,0,4,1,5,21,41,61,65,69,77,97,109,113],[257,32769,12289,275,69,41,16777857,2179200,1042,2116,131112,8389121,19,69,41,1042,2116,4194344,262150,524298,1048588])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p19_D6 : List StD := [
([pw0,pw1,pw2,pw46,pw6,pw21],[44,1,5,17,29,37,45,77,85,25,33,129,21,41,97,117,121,125,133,137,141,145,149,153,157],[32775,4234,66066,1186,8386,261,261,131077,261,2584,3112,278600,1572912,6291536,25165920]),
([pw0,pw1,pw2,pw4,pw47,pw21],[24,1,5,17,33,41,93,49,77,85,29,53,45,97,121,125,133,137,141,145,149,153,157,161],[8388615,259,16387,259,259,652,1604,34836,4644,1224,2200,73768,393296,1572960,6291504]),
([pw0,pw1,pw2,pw4,pw6,pw48],[24,44,1,5,29,33,41,77,85,129,17,37,73,93,97,121,125,133,137,141,145,149,153,157],[4111,133,32773,133,133,266,266,65546,266,9744,3616,148032,786480,3145808,12583008]),
([pw51,pw0,pw1,pw22,pw2,pw4,pw6],[21,29,33,9,45,37,93,17,13,41,76,25,53,61,73,165,169,173],[536,528,1024,145,82,52,16648,32768,137,2058,44,65536,131329,66,4100,129,66,36,67,37,8198]),
([pw51,pw0,pw1,pw2,pw4,pw6],[17,37,45,93,165,169,29,33,49,9,13,21,41,25,53,97,101,105,109,137,141,149,157,177,181,185],[4628,5156,34821,2097228,4194438,1584,67601,8396824,131218,262433,16777320,33570850,329,387,1572874])]
def p19_D5 : List StD := []
theorem p19_I5 : LevelN true p19_T 5 p19_D5 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p19_C6x0 : levelOK true p19_T p19_t 5 (p19_D5.map Prod.fst) ((p19_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p19_I6 : LevelN true p19_T 6 p19_D6 := levelStep p19_B p19_W p19_I5 (chunks 32 p19_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p19_C6x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p19_C7x0 : levelOK true p19_T p19_t 6 (p19_D6.map Prod.fst) ((p19_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p19_I7 : LevelN true p19_T 7 p19_D7 := levelStep p19_B p19_W p19_I6 (chunks 32 p19_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p19_C7x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p19_C8x0 : levelOK true p19_T p19_t 7 (p19_D7.map Prod.fst) ((p19_D8.drop (0*32)).take 32) = true := by decide +kernel
theorem p19_I8 : LevelN true p19_T 8 p19_D8 := levelStep p19_B p19_W p19_I7 (chunks 32 p19_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p19_C8x0
  ))
theorem p19_L : LowN true p19_R p19_T 9 := lowSearch p19_B p19_I8 (by decide +kernel)
def p20_T : Nat := 0xfefefeeefefafe00fefefeeefefafe00fefefeeefefafe00fefefeeefefafe00
def p20_R : List Nat := [0, 1, 2, 3, 4, 5]
def p20_E : List (Nat × Nat × Nat) := [(0,8,9),(1,8,10),(2,8,12),(3,1,9),(4,1,17),(5,1,33)]
theorem p20_B : baseOK p20_T p20_R p20_E = true := by decide +kernel
def p20_Z : List SliceD := [(pw7,5,[1, 2, 3, 4, 5]),(pw5,5,[4, 5, 0, 1, 2])]
theorem p20_Y : ∀ s ∈ p20_Z, SliceN true p20_R p20_T s := by
  unfold p20_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p20_B p10_B p10_L (by decide +kernel),mkSlice (w:=0) p20_B p10_B p10_L (by decide +kernel),by simp⟩
def p20_C : List (Nat × List Nat) := [(0,[]),(1,[])]
def p20_t : Tabs := (p20_C.map (mkCut true p20_Z),[(9,8),(10,8),(19,18),(37,36),(12,8),(38,36),(22,18),(9,1),(10,2),(17,1),(26,24),(19,3),(33,1),(34,2),(12,4),(20,4),(44,40),(37,5),(26,18),(44,36),(52,36),(50,18)],[],[[]])
theorem p20_W : TabsP true p20_R p20_T p20_t := ⟨cutsGood p20_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p20_D6 : List StD := [
([pw0,pw1,pw2,pw4,pw6,pw21],[0,1,5,17,29,37,49,9,21,25,4,13,33,41,45,53,57,61,65,69,73,77,81,85],[135,2051,131,131,2051,780,4372,24612,33092,66072,131624,786504,1049648,2098256,12583008])]
def p20_D5 : List StD := []
theorem p20_I5 : LevelN true p20_T 5 p20_D5 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p20_C6x0 : levelOK true p20_T p20_t 5 (p20_D5.map Prod.fst) ((p20_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p20_I6 : LevelN true p20_T 6 p20_D6 := levelStep p20_B p20_W p20_I5 (chunks 32 p20_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p20_C6x0
  ))
theorem p20_L : LowN true p20_R p20_T 7 := lowSearch p20_B p20_I6 (by decide +kernel)
def p21_T : Nat := 0xffffffffffffffccfffffff8faf8eac8ffffffffffffffccfffffff8faf8eac8
def p21_R : List Nat := [0, 1, 2, 3, 4, 5, 6]
def p21_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,1,9),(4,4,20),(5,4,36),(6,2,66)]
theorem p21_B : baseOK p21_T p21_R p21_E = true := by decide +kernel
def p21_Z : List SliceD := [(pw17,9,[3, 5, 4, 6, 2, 0]),(pw3,9,[6, 5, 0, 3, 1, 4]),(pw97,7,[1, 2, 4, 5, 0]),(pw98,7,[5, 4, 6, 3, 2]),(pw9,9,[1, 3, 5, 6, 2, 0]),(pw99,9,[2, 5, 0, 3, 1, 4]),(pw100,5,[4, 5, 2, 6]),(pw101,5,[6, 4, 5, 1]),(pw19,7,[1, 3, 4, 6, 2, 0])]
theorem p21_Y : ∀ s ∈ p21_Z, SliceN true p21_R p21_T s := by
  unfold p21_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p21_B p11_B p11_L (by decide +kernel),mkSlice (w:=0) p21_B p16_B p16_L (by decide +kernel),mkSlice (w:=0) p21_B p7_B p7_L (by decide +kernel),mkSlice (w:=0) p21_B p9_B p9_L (by decide +kernel),mkSlice (w:=0) p21_B p18_B p18_L (by decide +kernel),mkSlice (w:=0) p21_B p19_B p19_L (by decide +kernel),mkSlice (w:=1) p21_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p21_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p21_B p20_B p20_L (by decide +kernel),by simp⟩
def p21_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(0,[641]),(6,[]),(1,[393]),(4,[645]),(7,[]),(0,[645]),(1,[261]),(2,[525]),(5,[261]),(4,[649]),(1,[262]),(4,[650]),(0,[644]),(5,[262]),(0,[129]),(3,[385]),(1,[389]),(4,[261]),(8,[]),(3,[386]),(0,[131]),(1,[390]),(4,[263]),(0,[646]),(1,[262,537]),(5,[262,537]),(4,[650,25])]
def p21_t : Tabs := (p21_C.map (mkCut true p21_Z),[(3,1),(6,4),(21,17),(6,2),(40,32),(9,8),(9,1),(21,5),(19,2),(35,34),(37,5),(81,17),(66,2),(14,12),(3,17),(35,33),(14,10),(36,32),(72,12),(28,12),(40,8),(72,8),(48,32),(96,32),(13,12),(25,24),(19,17),(3,65),(13,5),(20,16),(25,17),(41,33),(9,65),(20,4),(66,18),(3,2),(6,12),(66,64),(9,5),(72,64),(6,18),(9,17),(19,18),(80,17),(9,12),(9,0),(3,18),(35,32)],[],[[]])
theorem p21_W : TabsP true p21_R p21_T p21_t := ⟨cutsGood p21_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p21_D10 : List StD := [
([pw0,pw1,pw2,pw4,pw6,pw21,pw102],[8,0,20,4,16,12,1,9,17,21,45,29,3,5,13,25,49,33,37,41,53,57,61,65,69,73,77,81,85,89,93],[8258,16520,37665,133680,791072,67109,8258,1048642,2097170,4194370,65542,8388744,16520,16777352,33554444,67111185,134254849,268436741,536872976,1045,1073742853])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p21_D9 : List StD := [
([pw0,pw1,pw2,pw4,pw56,pw6,pw21,pw102],[8,12,24,28,1,32,113,36,5,13,40,97,133,4,16,21,25,49,53,61,69,73,89,93,101,105,109,117,121,125,129,137],[276,34818,3,3,16779266,10,11,276,262149,276,33554452,524308,67108869,65601,8744,134218272,1049120,2097185,2,268435521,536870977,1073741897,20616,1032,1033,4198528,2147483777,8519681]),
([pw0,pw1,pw2,pw4,pw6,pw21,pw44,pw102],[28,52,44,1,12,48,56,17,9,60,5,13,25,49,133,157,61,69,73,89,93,105,121,137,141,145,149,153],[1036,2336,4243,17,17,16777233,19,1036,33554445,2097164,65548,1036,67108876,134217761,2336,131360,2336,262240,4194435,4227,32899,32963,541184,16897,8389186,16,1056834,8259]),
([pw20,pw0,pw1,pw2,pw4,pw6,pw21,pw102],[28,64,68,76,1,25,17,69,89,93,5,0,12,72,13,37,49,57,61,73,109,129,133,137,141,145,153,161,165,3],[32769,536872977,131,97,261,8193,521,1041,131,97,261,16781313,521,1027,33554481,131077,262161,1048585,67108867,134217734,16514,524298,268435461,97,2097161,4194564,8388620,66056]),
([pw0,pw1,pw2,pw4,pw6,pw21,pw103,pw102],[8,28,80,84,141,88,1,49,92,65,125,77,97,96,5,53,85,117,37,61,69,73,81,89,93,105,133,137,169,173],[16452,4122,5146,268435482,262170,4122,536871067,16452,32773,33554500,524356,32836,133,1571,131616,1049120,131616,2097185,3331,4202499,8193,66691,8390912,67111168,134217985,2,16777345,65665]),
([pw104,pw0,pw1,pw2,pw4,pw6,pw21,pw102],[8,100,28,104,108,112,1,96,141,93,13,69,89,25,37,61,5,17,57,73,81,109,129,137,145,153,161,165,173,177,181,185],[16646,32842,3088,131201,4256,4,641,65610,536873238,1073750279,2147488038,16646,268436231,1114,16777295,262250,32842,2097227,33554453,67108912,3088,524305,134217765,1048709,4203013,4256,8388641,641])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p21_D8 : List StD := [
([pw0,pw105,pw2,pw4,pw6,pw21,pw102],[28,1,141,124,25,120,116,128,97,117,12,5,13,17,49,69,73,89,93,105,113,121,129,133,137,145,149,169,189],[67,261,261,134217733,268435461,1029,2051,33554451,524291,67,67108867,1048593,4640,33312,65576,2097169,8209,4194313,8519808,16777352,278536])]
def p21_D7 : List StD := []
theorem p21_I7 : LevelN true p21_T 7 p21_D7 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p21_C8x0 : levelOK true p21_T p21_t 7 (p21_D7.map Prod.fst) ((p21_D8.drop (0*32)).take 32) = true := by decide +kernel
theorem p21_I8 : LevelN true p21_T 8 p21_D8 := levelStep p21_B p21_W p21_I7 (chunks 32 p21_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p21_C8x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p21_C9x0 : levelOK true p21_T p21_t 8 (p21_D8.map Prod.fst) ((p21_D9.drop (0*32)).take 32) = true := by decide +kernel
theorem p21_I9 : LevelN true p21_T 9 p21_D9 := levelStep p21_B p21_W p21_I8 (chunks 32 p21_D9 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p21_C9x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p21_C10x0 : levelOK true p21_T p21_t 9 (p21_D9.map Prod.fst) ((p21_D10.drop (0*32)).take 32) = true := by decide +kernel
theorem p21_I10 : LevelN true p21_T 10 p21_D10 := levelStep p21_B p21_W p21_I9 (chunks 32 p21_D10 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p21_C10x0
  ))
theorem p21_L : LowN true p21_R p21_T 11 := lowSearch p21_B p21_I10 (by decide +kernel)
def ptopT : Nat := 0xfffffffefffffffefffffffefffffffafffffefeffffeeeefefefefeeeee0000
def ptopR : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]
def ptopE : List (Nat × Nat × Nat) := [(0,16,17),(1,16,18),(2,32,36),(3,128,136),(4,1,17),(5,1,33),(6,1,65),(7,1,129)]
theorem ptopB : baseOK ptopT ptopR ptopE = true := by decide +kernel
def ptopZ : List SliceD := [(pw5,11,[2, 5, 1, 7, 6, 4, 0])]
theorem ptopY : ∀ s ∈ ptopZ, SliceN true ptopR ptopT s := by
  unfold ptopZ
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) ptopB p21_B p21_L (by decide +kernel),by simp⟩
def ptopC : List (Nat × List Nat) := [(0,[])]
def ptopt : Tabs := (ptopC.map (mkCut true ptopZ),[],[],[[]])
theorem ptopW : TabsP true ptopR ptopT ptopt := ⟨cutsGood ptopY (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD11 : List StD := [
([pw0,pw1,pw2,pw4,pw6,pw21,pw102,pw106],[0],[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])]
def ptopD10 : List StD := []
theorem ptopI10 : LevelN true ptopT 10 ptopD10 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC11x0 : levelOK true ptopT ptopt 10 (ptopD10.map Prod.fst) ((ptopD11.drop (0*32)).take 32) = true := by decide +kernel
theorem ptopI11 : LevelN true ptopT 11 ptopD11 := levelStep ptopB ptopW ptopI10 (chunks 32 ptopD11 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC11x0
  ))
theorem ptopL : LowN true ptopR ptopT 12 := lowSearch ptopB ptopI11 (by decide +kernel)

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
theorem excludes : Impossible true graph 11 theInputs.toFinset := by
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
  by_cases big : 13 ≤ gates.length
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

end PEqualNP.Outside.L_meta_15010

theorem PEqualNP.Outside.L_meta_15010 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 1, 6, 4, 6, 0, 7, 2, 7, 3, 7, 4, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact PEqualNP.Outside.L_meta_15010.replaceShort gates o fit correct
