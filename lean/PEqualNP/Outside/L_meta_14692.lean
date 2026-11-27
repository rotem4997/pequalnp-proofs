import PEqualNP.Defs

-- The live-set and restriction lemmas follow L-meta-10554, L-meta-10802, L-meta-1674, L-meta-670 and L-meta-1667.
-- The rectangle argument follows L-meta-8459.
namespace PEqualNP.Outside.L_meta_14692
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


def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[
    ⟨.or, [0, 7]⟩,
    ⟨.or, [0, 1]⟩,
    ⟨.or, [4, 7]⟩,
    ⟨.or, [1, 7]⟩,
    ⟨.or, [2, 11]⟩,
    ⟨.or, [0, 4]⟩,
    ⟨.or, [2, 13]⟩,
    ⟨.and, [3, 8]⟩,
    ⟨.and, [9, 10]⟩,
    ⟨.and, [14, 6]⟩,
    ⟨.and, [5, 12]⟩,
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
def pw3 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
def pw4 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00
def pw5 : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
def pw6 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
def pw7 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
def pw8 : Nat := 0x333300003333000033330000333300003333000033330000333300003333
def pw9 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
def pw10 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
def pw11 : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
def pw12 : Nat := 0x2222222222222222222222222222222222222222222222222222222222222222
def pw13 : Nat := 0xfafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafafa
def pw14 : Nat := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a
def pw15 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaaffaa
def pw16 : Nat := 0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa
def pw17 : Nat := 0xffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaaffffaaaa
def pw18 : Nat := 0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa
def pw19 : Nat := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc
def pw20 : Nat := 0xffccffccffccffccffccffccffccffccffccffccffccffccffccffccffccffcc
def pw21 : Nat := 0xfffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0fffff0f0
def pw22 : Nat := 0xffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00ffffff00
def pw23 : Nat := 0xfefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefefe
def pw24 : Nat := 0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e
def pw25 : Nat := 0xffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffeeffee
def pw26 : Nat := 0xee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee00ee
def pw27 : Nat := 0xeeee0000eeee0000eeee0000eeee0000eeee0000eeee0000eeee0000eeee
def pw28 : Nat := 0xf2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2
def pw29 : Nat := 0x202020202020202020202020202020202020202020202020202020202020202
def pw30 : Nat := 0xff22ff22ff22ff22ff22ff22ff22ff22ff22ff22ff22ff22ff22ff22ff22ff22
def pw31 : Nat := 0x22002200220022002200220022002200220022002200220022002200220022
def pw32 : Nat := 0x3232323232323232323232323232323232323232323232323232323232323232
def pw33 : Nat := 0xfa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa00fa
def pw34 : Nat := 0xfffffafafffffafafffffafafffffafafffffafafffffafafffffafafffffafa
def pw35 : Nat := 0xfafa0000fafa0000fafa0000fafa0000fafa0000fafa0000fafa0000fafa
def pw36 : Nat := 0xcececececececececececececececececececececececececececececececece
def pw37 : Nat := 0xffff0a0affff0a0affff0a0affff0a0affff0a0affff0a0affff0a0affff0a0a
def pw38 : Nat := 0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a
def pw39 : Nat := 0x3322332233223322332233223322332233223322332233223322332233223322
def pw40 : Nat := 0xf0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a
def pw41 : Nat := 0xffffffaaffffffaaffffffaaffffffaaffffffaaffffffaaffffffaaffffffaa
def pw42 : Nat := 0xffaa0000ffaa0000ffaa0000ffaa0000ffaa0000ffaa0000ffaa0000ffaa
def pw43 : Nat := 0xcceecceecceecceecceecceecceecceecceecceecceecceecceecceecceeccee
def pw44 : Nat := 0xffff00aaffff00aaffff00aaffff00aaffff00aaffff00aaffff00aaffff00aa
def pw45 : Nat := 0xaa000000aa000000aa000000aa000000aa000000aa000000aa000000aa
def pw46 : Nat := 0x3333222233332222333322223333222233332222333322223333222233332222
def pw47 : Nat := 0xf0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a0f0f0a0a
def pw48 : Nat := 0xff00aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa00ff00aa
def pw49 : Nat := 0xf0f0fafaf0f0fafaf0f0fafaf0f0fafaf0f0fafaf0f0fafaf0f0fafaf0f0fafa
def pw50 : Nat := 0xff00ffaaff00ffaaff00ffaaff00ffaaff00ffaaff00ffaaff00ffaaff00ffaa
def pw51 : Nat := 0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8
def pw52 : Nat := 0x5454545454545454545454545454545454545454545454545454545454545454
def pw53 : Nat := 0xaa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88aa88
def pw54 : Nat := 0x5544554455445544554455445544554455445544554455445544554455445544
def pw55 : Nat := 0xaaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0aaaaa0a0
def pw56 : Nat := 0x5555505055555050555550505555505055555050555550505555505055555050
def pw57 : Nat := 0xaaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00aaaaaa00
def pw58 : Nat := 0x5555550055555500555555005555550055555500555555005555550055555500
def pw59 : Nat := 0xfe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe00fe
def pw60 : Nat := 0xfefe0000fefe0000fefe0000fefe0000fefe0000fefe0000fefe0000fefe
def pw61 : Nat := 0xf0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e0f0e
def pw62 : Nat := 0xffee0000ffee0000ffee0000ffee0000ffee0000ffee0000ffee0000ffee
def pw63 : Nat := 0xf200f200f200f200f200f200f200f200f200f200f200f200f200f200f200f2
def pw64 : Nat := 0xf020f020f020f020f020f020f020f020f020f020f020f020f020f020f020f02
def pw65 : Nat := 0x3333323233333232333332323333323233333232333332323333323233333232
def pw66 : Nat := 0xff00fa00ff00fa00ff00fa00ff00fa00ff00fa00ff00fa00ff00fa00ff00fa
def pw67 : Nat := 0xcece0000cece0000cece0000cece0000cece0000cece0000cece0000cece
def pw68 : Nat := 0x3333020233330202333302023333020233330202333302023333020233330202
def pw69 : Nat := 0x3333332233333322333333223333332233333322333333223333332233333322
def pw70 : Nat := 0xf0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a0f0f0f0a
def pw71 : Nat := 0xccee0000ccee0000ccee0000ccee0000ccee0000ccee0000ccee0000ccee
def pw72 : Nat := 0x3333002233330022333300223333002233330022333300223333002233330022
def pw73 : Nat := 0xf000fa00f000fa00f000fa00f000fa00f000fa00f000fa00f000fa00f000fa
def pw74 : Nat := 0xf000f0a0f000f0a0f000f0a0f000f0a0f000f0a0f000f0a0f000f0a0f000f0a
def pw75 : Nat := 0xffa8ffa8ffa8ffa8ffa8ffa8ffa8ffa8ffa8ffa8ffa8ffa8ffa8ffa8ffa8ffa8
def pw76 : Nat := 0xffffa8a8ffffa8a8ffffa8a8ffffa8a8ffffa8a8ffffa8a8ffffa8a8ffffa8a8
def pw77 : Nat := 0xfaf8faf8faf8faf8faf8faf8faf8faf8faf8faf8faf8faf8faf8faf8faf8faf8
def pw78 : Nat := 0xffffaa88ffffaa88ffffaa88ffffaa88ffffaa88ffffaa88ffffaa88ffffaa88
def pw79 : Nat := 0xeeeeececeeeeececeeeeececeeeeececeeeeececeeeeececeeeeececeeeeecec
def pw80 : Nat := 0xffaaffa0ffaaffa0ffaaffa0ffaaffa0ffaaffa0ffaaffa0ffaaffa0ffaaffa0
def pw81 : Nat := 0xeeeeeecceeeeeecceeeeeecceeeeeecceeeeeecceeeeeecceeeeeecceeeeeecc
def pw82 : Nat := 0xfafafaf0fafafaf0fafafaf0fafafaf0fafafaf0fafafaf0fafafaf0fafafaf0
def pw83 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def pw84 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
def pw85 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def pw86 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def pw87 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
def pw88 : Nat := 0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc
def pw89 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0
def pw90 : Nat := 0xfc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc
def pw91 : Nat := 0xf0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c
def pw92 : Nat := 0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc
def pw93 : Nat := 0x3333303033333030333330303333303033333030333330303333303033333030
def pw94 : Nat := 0x8888888888888888888888888888888888888888888888888888888888888888
def pw95 : Nat := 0x4444444444444444444444444444444444444444444444444444444444444444
def pw96 : Nat := 0xff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88
def pw97 : Nat := 0xffff8888ffff8888ffff8888ffff8888ffff8888ffff8888ffff8888ffff8888
def pw98 : Nat := 0xffffffff88888888ffffffff88888888ffffffff88888888ffffffff88888888
def pw99 : Nat := 0xeeeeeeee00000000eeeeeeee00000000eeeeeeee00000000eeeeeeee
def pw100 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def pw101 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def pw102 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def pw103 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
def pw104 : Nat := 0xff000000ff0000000000000000000000ff000000ff
def pw105 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
def pw106 : Nat := 0xa0a0a0a000000000a0a0a0a000000000a0a0a0a000000000a0a0a0a
def pw107 : Nat := 0xcc000000cc000000cc000000cc000000cc000000cc000000cc000000cc
def pw108 : Nat := 0xff000000ff0000000000000000000000ff000000ff00
def pw109 : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f0
def pw110 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
def pw111 : Nat := 0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000
def pw112 : Nat := 0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000
def pw113 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000
def pw114 : Nat := 0xffffffffffffffffffffffff00000000ffffffffffffffffffffffff00000000
def pw115 : Nat := 0xffffffff000000000000000000000000ffffffff0000000000000000
def pw116 : Nat := 0xffffffffffff00000000000000000000ffffffffffff00000000000000000000
def pw117 : Nat := 0xffffffffffffffffffffffffffff0000ffffffffffffffffffffffffffff0000
def pw118 : Nat := 0xffffffffffff00000000000000000000ffffffffffff0000
def pw119 : Nat := 0xffff0000000000000000000000000000ffff0000000000000000
def pw120 : Nat := 0xff00ff00ff00ff00ff000000ff000000ff00ff00ff00ff00ff000000ff0000
def pw121 : Nat := 0xffffffff00000000ffff000000000000ffffffff00000000ffff0000
def pw122 : Nat := 0xffffffff0000ffffffffffff00000000ffffffff0000ffffffffffff00000000
def pw123 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f000000000f0f0f0f0f0f0f0f0f0f0f0f00000000
def pw124 : Nat := 0xffff0000ffff0000ffff000000000000ffff0000ffff0000ffff00000000
def pw125 : Nat := 0xffff0000ffffffffffff0000ffff0000ffff0000ffffffffffff0000ffff0000
def pw126 : Nat := 0xfffffffffffff0f0f0f0f0f0f0f0f0f0fffffffffffff0f0f0f0f0f0f0f0f0f0
def pw127 : Nat := 0xffffffffffffff00ff00ff00ff00ff00ffffffffffffff00ff00ff00ff00ff00
def pw128 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f00000f0f0f0f0f0f0f0f0f0f0f0f0f0f0000
def pw129 : Nat := 0xff00ff00ff00ff00ff00ff00ff000000ff00ff00ff00ff00ff00ff00ff0000
def pw130 : Nat := 0xffffffff00ff00ffffffffff00ff0000ffffffff00ff00ffffffffff00ff0000
def pw131 : Nat := 0xf0f0f0f00000f0f0f0f0f0f000000000f0f0f0f00000f0f0f0f0f0f00000000
def pw132 : Nat := 0xffff0f0fffff0f0fffff0f0fffff0000ffff0f0fffff0f0fffff0f0fffff0000
def pw133 : Nat := 0xff000000ff00ff00ff000000ff000000ff000000ff00ff00ff000000ff0000
def pw134 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff0000
def pw135 : Nat := 0xf0f0f0f000f000f0f0f0f0f000f00000f0f0f0f000f000f0f0f0f0f000f0000
def pw136 : Nat := 0xff000f00ff000f00ff000f00ff000000ff000f00ff000f00ff000f00ff0000
def pw137 : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
def pw138 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def pw139 : Nat := 0x111111111111111100000000000000001111111111111111
def pw140 : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
def pw141 : Nat := 0x44444444000000004444444400000000444444440000000044444444
def pw142 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0
def pw143 : Nat := 0x3030303030303030303030303030303030303030303030303030303030303030
def pw144 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def pw145 : Nat := 0x3333000033330000333300003333000033330000333300003333000033330000
def pw146 : Nat := 0x5555555500000000555555550000000055555555000000005555555500000000
def pw147 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00
def pw148 : Nat := 0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa
def pw149 : Nat := 0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc
def pw150 : Nat := 0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc
def pw151 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0
def pw152 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0
def pw153 : Nat := 0xcccccccceeeeeeeecccccccceeeeeeeecccccccceeeeeeeecccccccceeeeeeee
def pw154 : Nat := 0xf0f0f0f0fafafafaf0f0f0f0fafafafaf0f0f0f0fafafafaf0f0f0f0fafafafa
def pw155 : Nat := 0xaaaaeeeeaaaaeeeeaaaaeeeeaaaaeeeeaaaaeeeeaaaaeeeeaaaaeeeeaaaaeeee
def pw156 : Nat := 0xf0f0fcfcf0f0fcfcf0f0fcfcf0f0fcfcf0f0fcfcf0f0fcfcf0f0fcfcf0f0fcfc
def pw157 : Nat := 0xf0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c
def pw158 : Nat := 0xaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafa
def pw159 : Nat := 0xccfcccfcccfcccfcccfcccfcccfcccfcccfcccfcccfcccfcccfcccfcccfcccfc
def pw160 : Nat := 0x3333333330303030333333333030303033333333303030303333333330303030
def pw161 : Nat := 0xccccaaaaeeee0000ccccaaaaeeee0000ccccaaaaeeee0000ccccaaaaeeee
def pw162 : Nat := 0xf000f0aafaaafa00f000f0aafaaafa00f000f0aafaaafa00f000f0aafaaafa
def pw163 : Nat := 0xf0ccfc00f0ccfc00f0ccfc00f0ccfc00f0ccfc00f0ccfc00f0ccfc00f0ccfc
def pw164 : Nat := 0xffffffffffffffffffffffffffffffff
def pw165 : Nat := 0x555555555555555500000000000000005555555555555555
def pw166 : Nat := 0x550055005500550055005500550055
def pw167 : Nat := 0x5555555555555555000000000000000055555555555555550000000000000000
def pw168 : Nat := 0xffffffff00000000ffffffff00000000
def pw169 : Nat := 0xffffffff00000000ffffffff
def pw170 : Nat := 0xffffffffffffffff
def pw171 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000
def pw172 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def pw173 : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
def pw174 : Nat := 0x33333333000000003333333300000000333333330000000033333333
def pw175 : Nat := 0x55005500550055005500550055005500
def pw176 : Nat := 0xffff0000ffff00000000000000000000ffff0000ffff
def pw177 : Nat := 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000
def pw178 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa
def pw179 : Nat := 0xffffffffffffffffaaaaaaaaaaaaaaaaffffffffffffffffaaaaaaaaaaaaaaaa
def pw180 : Nat := 0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def pw181 : Nat := 0xffffffffffffffffffffffffffffffffffffffff00000000ffffffff00000000
def pw182 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000
def pw183 : Nat := 0xffffffffffffffffffffffffaaaaaaaaffffffffffffffffffffffffaaaaaaaa
def pw184 : Nat := 0xffffffffaaaaaaaa0000000000000000ffffffffaaaaaaaa
def pw185 : Nat := 0xffffffffffffffffffffffffffffffffffffffffaaaaaaaaffffffffaaaaaaaa
def pw186 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaa
def pw187 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaa
def pw188 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00aa00aa00aa00aa00aa00aa00aa00aa
def pw189 : Nat := 0x5555555555555555555555550000000055555555555555555555555500000000
def pw190 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000
def pw191 : Nat := 0xffffffffffffffffffffffff00000000
def pw192 : Nat := 0x5555555555555555555555555555555555555555555555550000000000000000
def pw193 : Nat := 0xffffffff00000000ffffffff00000000ffffffff0000000000000000
def pw194 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a0f0f0f0f0f0f0f0f0f0f0f0f0a0a0a0a
def pw195 : Nat := 0xffffffffffffffffffffffffffffffff0000000000000000ffffffffaaaaaaaa
def pw196 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000
def pw197 : Nat := 0xaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaaaaaaaaa
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
def p2_T : Nat := 0xeae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8eae8
def p2_R : List Nat := [0, 1, 2, 3]
def p2_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
theorem p2_B : baseOK p2_T p2_R p2_E = true := by decide +kernel
def p2_Z : List SliceD := [(pw3,4,[0, 1, 2])]
theorem p2_Y : ∀ s ∈ p2_Z, SliceN true p2_R p2_T s := by
  unfold p2_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p2_B p1_B p1_L (by decide +kernel),by simp⟩
def p2_C : List (Nat × List Nat) := [(0,[])]
def p2_t : Tabs := (p2_C.map (mkCut true p2_Z),[(5,4),(6,4),(3,2),(3,1),(6,2),(5,1)],[],[[]])
theorem p2_W : TabsP true p2_R p2_T p2_t := ⟨cutsGood p2_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p2_D4 : List StD := [
([pw0,pw1,pw2,pw4],[0,1,5,17,9,13,21],[54,90,3,108,5,9])]
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
def p3_T : Nat := 0xfeeefaa8feeefaa8feeefaa8feeefaa8feeefaa8feeefaa8feeefaa8feeefaa8
def p3_R : List Nat := [0, 1, 2, 3, 4]
def p3_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,1,17)]
theorem p3_B : baseOK p3_T p3_R p3_E = true := by decide +kernel
def p3_Z : List SliceD := [(pw5,5,[0, 2, 3, 4]),(pw6,5,[0, 1, 4, 3]),(pw3,5,[0, 1, 4, 2]),(pw7,5,[0, 2, 3, 1]),(pw8,4,[0, 2, 3]),(pw9,4,[0, 1, 4])]
theorem p3_Y : ∀ s ∈ p3_Z, SliceN true p3_R p3_T s := by
  unfold p3_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p3_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p3_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p3_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p3_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p3_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p3_B p1_B p1_L (by decide +kernel),by simp⟩
def p3_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(0,[384]),(0,[386]),(0,[389]),(0,[393])]
def p3_t : Tabs := (p3_C.map (mkCut true p3_Z),[(18,16),(3,2),(3,1),(12,8),(5,4),(5,1),(12,4),(9,8),(9,1),(18,2),(17,16),(17,1),(22,20),(14,10),(26,24),(14,6),(28,24),(22,6),(28,20),(26,10),(7,6),(11,10),(21,20),(25,24),(12,6),(18,6),(18,10),(12,10),(18,20),(12,20),(18,24),(12,24),(5,6),(18,0),(3,6),(5,2),(9,10),(11,2),(7,2),(3,10),(9,2),(17,0),(22,4),(26,8),(7,1),(14,8),(14,4),(11,1),(5,0),(12,0),(17,20),(11,6),(7,4),(5,20),(17,4),(28,16),(9,0),(14,2),(7,10),(17,24),(11,8),(21,16),(9,24),(17,8),(3,0),(22,16),(26,16),(12,16),(12,2),(11,0),(18,8),(3,4),(18,4),(7,0),(3,8),(9,16),(5,16),(5,8),(3,16),(9,4),(17,2)],[],[[]])
theorem p3_W : TabsP true p3_R p3_T p3_t := ⟨cutsGood p3_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p3_D7 : List StD := [
([pw0,pw1,pw2,pw4,pw10],[3,0,4,1,8,12,13,25,9,21,37,16,20,5,17,29,33,41,45,49,53,57,61,65,69,73,77],[8459,16965,98449,394273,1572879,6291483,3338,4804,25165925,100663473])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p3_D6 : List StD := [
([pw0,pw1,pw11,pw2,pw4,pw10],[3,0,16,37,5,13,25,21,33,20,9,1,45,53,61,69,77,81,85],[19,2,131248,262480,4124,2051,9219,17411,14,673,833,13,480,32812,65612]),
([pw12,pw0,pw1,pw2,pw4,pw10],[0,16,13,25,45,3,5,21,33,37,20,49,1,9,57,69,77,81,85],[1,8225,1188,1320,530,97,131268,262472,530,6145,18433,515,396,32790,65562]),
([pw0,pw1,pw2,pw13,pw4,pw10],[20,3,1,33,17,9,37,45,21,25,0,16,13,49,61,69,73,81,89],[131124,19,1,537,262352,8455,1062,16397,228,4099,521,33027,11,2242,65545]),
([pw14,pw0,pw1,pw2,pw4,pw10],[20,33,3,1,9,17,25,37,45,53,0,16,13,21,61,65,73,81,89],[1,1052,8197,67,2436,131128,37,67,262560,4609,16387,408,67,33281,65539]),
([pw0,pw1,pw2,pw4,pw15,pw10],[20,3,1,13,29,9,37,45,21,33,0,16,25,53,57,65,77,85,93],[131124,281,19,1,262352,8205,16903,1062,228,265,11,32777,4099,66051,2242]),
([pw16,pw0,pw1,pw2,pw4,pw10],[20,21,3,1,9,13,29,37,45,61,0,16,25,33,53,65,73,85,93],[1,1052,35,8197,2436,131160,35,69,262592,16387,4609,408,35,32771,66049]),
([pw0,pw1,pw2,pw4,pw10,pw17],[16,3,1,41,13,21,25,33,20,9,45,37,49,57,65,73,89,93],[525,65592,131272,11,1,4101,8197,517,7,240,17411,306,33795,450,2051]),
([pw18,pw0,pw1,pw2,pw4,pw10],[16,9,3,1,13,21,25,33,41,20,69,37,45,49,57,77,89,93],[1,11,564,708,4101,11,65840,131520,261,8195,16387,11,240,3073,33793]),
([pw0,pw1,pw2,pw19,pw4,pw10],[20,0,17,16,25,33,37,49,53,3,5,45,29,41,97,101,105],[1670,1797,4612,53,10308,3,1,16515,202,2,305,33033,49,2120,65545]),
([pw0,pw1,pw2,pw4,pw20,pw10],[20,0,17,16,13,5,21,37,57,3,45,61,29,41,101,105,109],[806,116,6661,548,9348,65795,3,1,394,81,81,16409,2,34825,1160]),
([pw0,pw1,pw2,pw4,pw10,pw21],[20,16,1,17,5,9,25,33,65,3,41,69,97,113,117],[60,793,201,3594,536,8455,4103,38,38,449,3,2,16387,193,1]),
([pw0,pw1,pw2,pw4,pw10,pw22],[16,20,1,13,17,9,21,3,5,29,73,41,77,109,121,125],[308,344,1682,6289,656,8207,17415,37,37,74,32779,74,3,1,2])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p3_D5 : List StD := [
([pw12,pw0,pw11,pw2,pw4,pw10],[21,45,13,33,9,25,0,37,16,101,105,129,133],[2048,64,21,56,146,64,5,40,130,5,40,4354,5,515,1034]),
([pw0,pw11,pw2,pw19,pw4,pw10],[33,45,5,9,49,25,53,16,37,20,17,101,105,109,137,141,145,149],[1024,49156,65548,131077,262,8272,536,49,146,128,97,2114,41,266,4099]),
([pw0,pw11,pw2,pw4,pw20,pw10],[21,45,5,9,13,57,16,37,61,20,17,97,101,105,129,153,157,161],[1024,32773,196612,16396,134,17,2336,552,98,17,17,4099,64,8450,138]),
([pw0,pw1,pw2,pw23,pw4,pw10],[33,45,9,17,5,21,37,3,16,20,1,13,25,29,97,101,105,109,149],[28,24,8192,262153,74,131108,1024,16389,70,2048,4097,32802,641,386,65539]),
([pw24,pw0,pw1,pw2,pw4,pw10],[17,25,49,69,5,9,33,45,21,97,105],[17,36,256,66,136,17,17,67,137,36,518,36,66,136,1034]),
([pw0,pw1,pw2,pw4,pw25,pw10],[21,45,5,9,33,37,3,16,20,1,13,17,25,29,97,101,105,109,129,153],[262156,524293,8212,2048,38,131081,16408,512,42,1025,321,32771,4096,65554,194]),
([pw26,pw0,pw1,pw2,pw4,pw10],[13,29,57,77,5,9,21,45,33,101,109],[18,36,65,256,136,18,67,18,138,1029,36,36,65,521,136]),
([pw27,pw0,pw1,pw11,pw2,pw4],[21,5,13,33,37,25,45,24,9,53,61,129,133,165],[82,80,128,21,56,2306,8192,7,42,4096,513,1032,5,40,5]),
([pw27,pw0,pw1,pw2,pw4],[13,25,37,133,165,21,33,5,9,45,53,61,69,77,81,85,169,173],[660,780,4133,8262,408,16433,32850,66569,133130,99]),
([pw0,pw1,pw2,pw28,pw4,pw10],[17,33,45,5,37,49,20,1,9,13,21,25,69,97,105,149,177,3],[9,9,9,32771,21,66592,416,8226,20,512,2050,4100,131138,20,16390]),
([pw29,pw0,pw1,pw2,pw4,pw10],[25,37,33,45,5,13,17,9,21,29,97,101,105,109,181,185],[512,128,256,5,10,80,80,5,10,24608,33793,10,5,2082,4099]),
([pw0,pw1,pw2,pw4,pw30,pw10],[21,29,45,5,37,57,20,1,9,13,25,33,77,101,109,153,181,189,3],[10,32771,10,10,22,81921,133152,416,20,513,262209,8197,1024,4100,20]),
([pw31,pw0,pw1,pw2,pw4,pw10],[13,37,21,45,5,25,29,9,17,33,97,101,105,109,181,185],[256,128,5,512,10,80,5,80,10,24577,33824,10,5,2051,4130]),
([pw14,pw0,pw1,pw13,pw4,pw10],[9,33,1,45,21,37,25,0,20,97,105,137,193,197],[2048,21,128,82,56,5,4096,66,40,5,515,5,8450,40,1034]),
([pw0,pw1,pw13,pw19,pw4,pw10],[33,45,17,21,37,53,49,0,20,5,9,25,97,105,109,137,201,205],[32772,512,65548,131077,22,16480,1024,4161,18,168,289,18,2057,26,8195]),
([pw32,pw0,pw1,pw2,pw4,pw10],[5,37,53,61,17,21,33,45,9,101,105],[17,256,36,72,130,17,17,73,131,36,72,130,36,518,1034]),
([pw0,pw1,pw13,pw4,pw10,pw21],[9,33,17,20,1,21,25,65,16,5,69,97,101,117,137,209,213,217,221],[32773,512,70,196612,16420,17,2051,17,17,262154,5248,416,8202,66,8]),
([pw33,pw0,pw1,pw2,pw13,pw10],[9,20,17,25,37,45,33,1,49,69,97,197,209],[76,1033,72,2,56,4101,6,2,52,257,129,49,2048,514,48]),
([pw33,pw0,pw1,pw2,pw10],[1,25,37,197,225,9,45,17,21,33,49,61,69,73,81,89,221,229],[658,2083,778,8262,16433,408,32852,132105,101,69644]),
([pw0,pw1,pw2,pw4,pw10,pw34],[9,33,17,21,45,25,3,0,20,1,5,13,37,41,97,101,113,117,137,209],[524293,262156,38,8212,1024,65545,16387,513,193,42,32792,2048,131090,322,4096]),
([pw35,pw0,pw1,pw2,pw4,pw10],[1,41,65,73,9,17,21,33,45,97,113],[34,17,68,136,256,19,34,138,34,1029,521,17,68,68,136]),
([pw0,pw1,pw36,pw2,pw4,pw10],[17,33,45,9,53,5,37,61,16,1,13,21,25,101,105,149,177,3],[41,33,33,32771,69,512,65560,138,76,3088,4098,131332,146,8212,16390]),
([pw0,pw1,pw2,pw4,pw10,pw37],[9,13,17,33,25,41,65,0,1,37,45,73,97,109,193,209,3],[32773,16390,28,1060,36,8195,4105,257,65665,26,66,66,2056,24,512]),
([pw38,pw0,pw1,pw2,pw4,pw10],[1,25,9,13,33,17,37,5,21,41,45,97,101,105,109,193],[128,5,256,18,1024,5,32808,18,544,16393,2051,5,18,4168,8258]),
([pw16,pw0,pw1,pw2,pw15,pw10],[9,21,1,45,33,37,13,0,20,101,109,157,197,225],[2048,21,82,128,56,5,66,8192,40,1027,5,5,4354,522,40]),
([pw0,pw1,pw2,pw15,pw20,pw10],[21,45,29,37,33,61,0,20,5,9,13,57,97,101,109,157,181,233,237],[32772,131077,256,262164,14,81921,6176,512,10,161,1025,8195,112,10,26]),
([pw39,pw0,pw1,pw2,pw4,pw10],[5,37,53,21,29,45,61,33,9,101,105],[17,256,12,192,34,17,13,17,35,12,192,34,12,518,1090]),
([pw40,pw0,pw1,pw4,pw15,pw10],[9,20,13,37,45,21,29,1,57,77,109,197,241],[36,1029,36,2,28,4161,66,2,24,257,129,25,2048,514,24]),
([pw40,pw0,pw1,pw4,pw10],[1,13,37,193,197,9,45,21,29,33,53,57,65,77,153,221,229,245],[394,1059,658,4166,16425,792,131148,67601,101,40980]),
([pw0,pw1,pw2,pw15,pw10,pw22],[9,21,29,20,1,13,33,73,16,5,77,105,109,125,157,221,241,249,253],[65541,38,512,393220,16452,4099,17,17,17,32778,8202,34,3200,448,8]),
([pw0,pw1,pw2,pw4,pw10,pw41],[9,21,29,33,45,13,3,0,20,1,5,25,37,41,105,109,121,125,157,241],[524293,38,262156,8212,1024,32771,65545,513,193,34,131090,322,16408,2048,4096]),
([pw42,pw0,pw1,pw2,pw4,pw10],[1,41,65,21,9,29,73,33,45,109,121],[34,17,12,192,256,19,14,34,34,517,1089,17,12,12,192]),
([pw0,pw1,pw43,pw2,pw4,pw10],[5,21,45,9,61,29,37,53,16,1,13,25,33,101,105,129,153,189,3],[32777,33,65539,33,69,512,138,131096,76,1026,6160,262404,130,8198,16404]),
([pw0,pw1,pw2,pw4,pw10,pw44],[9,21,29,25,13,41,73,0,1,37,45,65,97,109,225,241,3],[32773,22,16396,1060,36,8195,4105,257,65665,18,2050,18,72,72,512]),
([pw45,pw0,pw1,pw2,pw4,pw10],[1,13,9,21,25,29,37,5,33,41,45,97,101,105,109,225],[128,5,10,256,1024,5,10,32816,544,16387,2065,5,10,4162,8272]),
([pw18,pw0,pw1,pw2,pw4,pw17],[9,21,13,33,25,45,1,0,28,97,109,133,165,213],[8192,97,38,56,128,65,6,24,4096,1027,521,2305,6,6,24]),
([pw46,pw0,pw2,pw4,pw10,pw17],[21,1,13,33,25,9,0,41,45,65,73,133,213,257],[34,7,26,34,64,5,24,4480,8192,5,513,5,1032,24,2048]),
([pw46,pw0,pw2,pw4,pw10],[1,13,25,133,257,21,33,9,41,45,49,57,65,73,169,173,209,241],[401,1059,2117,649,65586,131156,792,102,20490,40972]),
([pw0,pw1,pw2,pw4,pw17,pw21],[9,33,25,41,1,45,69,20,32,5,21,65,97,101,113,169,213,249,261],[25,65544,14,512,131112,278529,4099,33025,17,6,10304,1024,6,6,224]),
([pw47,pw0,pw1,pw2,pw4,pw10],[17,25,49,9,33,41,69,45,21,97,117],[33,12,256,18,192,13,33,19,33,12,518,12,18,192,1090]),
([pw0,pw1,pw2,pw4,pw17,pw22],[9,21,13,41,1,45,77,20,36,5,33,73,105,109,121,173,213,249,265],[25,14,131080,512,65576,8195,278529,33025,17,6,6,6,6208,1024,224]),
([pw48,pw0,pw1,pw2,pw4,pw10],[13,29,57,9,21,41,77,45,33,109,125],[34,12,17,256,192,14,19,34,34,517,12,12,17,1089,192]),
([pw0,pw1,pw2,pw49,pw4,pw10],[9,17,33,21,69,25,37,41,49,20,1,13,97,105,137,209,3],[32771,16394,130,38,130,257,1025,4101,257,2048,44,88,66052,80,8212]),
([pw0,pw1,pw2,pw4,pw50,pw10],[9,21,29,37,20,13,33,41,57,77,1,25,101,109,157,241,3],[32773,38,16452,132,132,8195,257,1025,257,34,65554,4106,2048,584,536]),
([pw51,pw0,pw1,pw2,pw4,pw10],[1,33,45,13,20,29,25,3,0,16,5,9,97,101,105,109,133,145,165,201],[1024,2065,272,146,644,131105,524328,66,262180,32777,4099,65541,74,8204,16390]),
([pw52,pw0,pw1,pw2,pw4,pw10],[9,21,33,45,49,53,25,37,5,97,101,105],[256,17,34,68,136,17,34,68,136,17,517,17,34,1034,2060]),
([pw53,pw0,pw1,pw2,pw4,pw10],[1,21,45,20,17,25,13,3,0,16,5,9,97,101,105,109,129,133,165,237],[1024,2057,138,264,644,65553,66,524336,262164,32771,4129,131077,66,8198,16420]),
([pw54,pw0,pw1,pw2,pw4,pw10],[9,21,45,57,13,33,37,61,5,101,105,109],[256,9,18,160,68,9,18,160,68,2051,9,9,18,518,1060]),
([pw55,pw0,pw1,pw2,pw4,pw10],[9,13,33,29,37,16,20,3,0,5,17,21,97,101,105,109,133,137,197,249,257],[1024,385,2082,196,96,1048585,131082,524,524312,32771,4101,65553,262150,8210,16404]),
([pw56,pw0,pw1,pw2,pw4,pw10],[9,21,33,65,1,45,25,69,17,97,113,117],[256,17,10,68,160,17,10,68,160,1027,517,17,10,10,2084]),
([pw57,pw0,pw1,pw2,pw4,pw10],[9,21,17,25,37,20,16,3,0,5,29,97,101,105,109,133,157,197,213,257],[1024,385,162,96,96,524293,518,65548,262164,16387,2057,32785,131082,4114,8216]),
([pw58,pw0,pw1,pw2,pw4,pw10],[9,21,33,1,13,45,73,77,29,109,121,125],[256,9,18,68,160,9,18,68,160,515,1029,9,18,2082,68])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p3_D4 : List StD := [
([pw59,pw0,pw1,pw2,pw10],[21,45,225,9,33,5,37,197,97,105,109,269],[36,280,145,530,36,133,70,1033,74,2051]),
([pw60,pw0,pw1,pw2,pw4],[21,33,165,9,45,5,13,17,25,97,105,109,133,149],[36,4120,81,1042,36,133,8198,2057,522,259]),
([pw61,pw0,pw1,pw4,pw10],[33,45,193,9,21,5,37,197,97,101,109,269],[36,1048,145,530,36,133,70,265,74,2051]),
([pw62,pw0,pw1,pw2,pw4],[21,165,9,33,45,5,13,25,29,97,101,109,133,153],[34,4116,1041,152,34,8195,266,2053,524,65]),
([pw63,pw0,pw1,pw2,pw10],[5,45,17,21,37,33,9,97,177,197,269,273],[5,192,552,50,5,5,19,2312,18,1034]),
([pw64,pw0,pw1,pw4,pw10],[5,21,45,29,33,37,9,109,189,197,269,273],[11,194,530,38,9,9,37,2320,36,1044]),
([pw65,pw0,pw2,pw4,pw10],[9,33,45,257,21,17,133,13,25,97,101,277,281],[41,145,515,69,40,2058,76,274,1044,4102]),
([pw66,pw0,pw1,pw2,pw10],[9,225,21,33,45,17,1,37,41,97,101,197,209,273],[34,521,2060,152,4099,34,274,8197,65,1044]),
([pw67,pw0,pw1,pw2,pw4],[17,33,5,9,13,25,45,21,53,61,133],[5,1096,208,98,5,5,35,280,522,50]),
([pw68,pw0,pw2,pw4,pw10],[9,13,33,45,257,25,133,21,29,281,285,289],[273,131,37,73,1042,52,88,38,2058,524]),
([pw69,pw0,pw2,pw4,pw10],[9,21,45,257,33,133,13,17,25,29,105,109,289,293],[137,2051,273,37,8202,536,44,66,4102,1044]),
([pw70,pw0,pw1,pw4,pw10],[9,21,33,193,45,197,1,5,37,41,105,109,273,293],[138,2051,38,274,8201,44,536,4101,65,1044]),
([pw71,pw0,pw1,pw2,pw4],[21,29,5,9,13,45,25,33,53,61,133],[6,1064,49,224,6,19,6,265,584,17]),
([pw72,pw0,pw2,pw4,pw10],[9,21,45,257,13,25,133,17,33,281,289,297],[137,19,289,69,26,2088,76,18,1030,548]),
([pw73,pw0,pw1,pw2,pw10],[9,37,225,21,33,17,45,97,133,197,209,269,273,301],[36,145,536,82,1029,36,8198,4105,259,2058]),
([pw74,pw0,pw1,pw4,pw10],[9,21,33,37,193,197,5,45,109,133,269,273,293,305],[82,259,38,138,4113,52,8216,2053,521,1036]),
([pw0,pw1,pw2,pw75,pw10],[25,29,45,13,5,9,33,37,97,101,105,109,157,165,181,201,309],[4098,98306,19,8198,18440,289,132,65,524,1029]),
([pw0,pw1,pw2,pw4,pw76],[29,13,33,45,213,37,97,101,105,109,145,181,185,197,313],[17409,17,17,17,2562,4164,40,8198,138,268]),
([pw0,pw1,pw77,pw4,pw10],[13,17,45,25,5,9,21,37,97,101,105,109,137,165,185,237,317],[4098,19,98306,8198,2081,16648,132,65,517,1036]),
([pw0,pw1,pw2,pw4,pw78],[13,17,45,25,249,21,37,97,101,105,109,129,181,185,193,313],[34818,16387,18,18,5121,8328,68,33,261,524]),
([pw0,pw79,pw2,pw4,pw10],[9,29,33,37,5,13,21,25,45,97,101,105,109,137,141,249,257,321],[65539,24578,18,163842,4161,517,265,132,1064,2060]),
([pw0,pw1,pw2,pw80,pw10],[9,29,13,33,37,5,21,97,101,105,109,133,137,249,253,257,309],[32771,69634,34,24578,1029,137,2065,76,276,536]),
([pw0,pw81,pw2,pw4,pw10],[9,17,21,37,25,5,33,45,97,101,105,109,157,161,197,213,257,321],[65539,34,12290,163842,2053,321,137,16404,524,1048]),
([pw0,pw1,pw82,pw4,pw10],[9,17,21,25,37,5,33,97,101,105,109,133,157,213,217,257,317],[32771,34,69634,24578,1029,137,2065,76,276,536])]
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p3_C5x0 : levelOK true p3_T p3_t 4 (p3_D4.map Prod.fst) ((p3_D5.drop (0*32)).take 32) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p3_C5x1 : levelOK true p3_T p3_t 4 (p3_D4.map Prod.fst) ((p3_D5.drop (1*32)).take 32) = true := by decide +kernel
theorem p3_I5 : LevelN true p3_T 5 p3_D5 := levelStep p3_B p3_W p3_I4 (chunks 32 p3_D5 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p3_C5x0
  · exact p3_C5x1
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p3_C6x0 : levelOK true p3_T p3_t 5 (p3_D5.map Prod.fst) ((p3_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p3_I6 : LevelN true p3_T 6 p3_D6 := levelStep p3_B p3_W p3_I5 (chunks 32 p3_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p3_C6x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p3_C7x0 : levelOK true p3_T p3_t 6 (p3_D6.map Prod.fst) ((p3_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p3_I7 : LevelN true p3_T 7 p3_D7 := levelStep p3_B p3_W p3_I6 (chunks 32 p3_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p3_C7x0
  ))
theorem p3_L : LowN true p3_R p3_T 8 := lowSearch p3_B p3_I7 (by decide +kernel)
def p4_T : Nat := 0xfeeefeeafeeefcc8feeefeeafeeefcc8feeefeeafeeefcc8feeefeeafeeefcc8
def p4_R : List Nat := [0, 1, 2, 3, 4, 5]
def p4_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,2,10),(4,1,17),(5,1,33)]
theorem p4_B : baseOK p4_T p4_R p4_E = true := by decide +kernel
def p4_Z : List SliceD := [(pw83,8,[1, 0, 2, 3, 4])]
theorem p4_Y : ∀ s ∈ p4_Z, SliceN true p4_R p4_T s := by
  unfold p4_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p4_B p3_B p3_L (by decide +kernel),by simp⟩
def p4_C : List (Nat × List Nat) := [(0,[])]
def p4_t : Tabs := (p4_C.map (mkCut true p4_Z),[],[],[[]])
theorem p4_W : TabsP true p4_R p4_T p4_t := ⟨cutsGood p4_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p4_D8 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw84],[0],[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])]
def p4_D7 : List StD := []
theorem p4_I7 : LevelN true p4_T 7 p4_D7 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p4_C8x0 : levelOK true p4_T p4_t 7 (p4_D7.map Prod.fst) ((p4_D8.drop (0*32)).take 32) = true := by decide +kernel
theorem p4_I8 : LevelN true p4_T 8 p4_D8 := levelStep p4_B p4_W p4_I7 (chunks 32 p4_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p4_C8x0
  ))
theorem p4_L : LowN true p4_R p4_T 9 := lowSearch p4_B p4_I8 (by decide +kernel)
def p5_T : Nat := 0xeeeaece8eeeaece8eeeaece8eeeaece8eeeaece8eeeaece8eeeaece8eeeaece8
def p5_R : List Nat := [0, 1, 2, 3, 4]
def p5_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,2,10),(4,1,17)]
theorem p5_B : baseOK p5_T p5_R p5_E = true := by decide +kernel
def p5_Z : List SliceD := [(pw3,5,[0, 1, 2, 4])]
theorem p5_Y : ∀ s ∈ p5_Z, SliceN true p5_R p5_T s := by
  unfold p5_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p5_B p2_B p2_L (by decide +kernel),by simp⟩
def p5_C : List (Nat × List Nat) := [(0,[])]
def p5_t : Tabs := (p5_C.map (mkCut true p5_Z),[(5,4),(6,4),(3,2),(3,1),(6,2),(5,1),(10,2),(13,12)],[],[[]])
theorem p5_W : TabsP true p5_R p5_T p5_t := ⟨cutsGood p5_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p5_D5 : List StD := [
([pw0,pw1,pw2,pw4,pw10],[0,1,5,17,25,9,13,21,29],[102,170,275,3,204,5,5,25,9,17])]
def p5_D4 : List StD := []
theorem p5_I4 : LevelN true p5_T 4 p5_D4 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p5_C5x0 : levelOK true p5_T p5_t 4 (p5_D4.map Prod.fst) ((p5_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p5_I5 : LevelN true p5_T 5 p5_D5 := levelStep p5_B p5_W p5_I4 (chunks 32 p5_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p5_C5x0
  ))
theorem p5_L : LowN true p5_R p5_T 6 := lowSearch p5_B p5_I5 (by decide +kernel)
def p6_T : Nat := 0xfeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeeafeea
def p6_R : List Nat := [0, 1, 2, 3]
def p6_E : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6),(3,2,10)]
theorem p6_B : baseOK p6_T p6_R p6_E = true := by decide +kernel
def p6_Z : List SliceD := [(pw85,4,[1, 2, 3])]
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
def p7_T : Nat := 0xfffefeeefffefeeefffefeeefffefeeefffefeeefffefeeefffefeeefffefeee
def p7_R : List Nat := [0, 1, 2, 3, 4]
def p7_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,8,12),(3,4,12),(4,4,20)]
theorem p7_B : baseOK p7_T p7_R p7_E = true := by decide +kernel
def p7_Z : List SliceD := [(pw85,5,[1, 2, 3, 4])]
theorem p7_Y : ∀ s ∈ p7_Z, SliceN true p7_R p7_T s := by
  unfold p7_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p7_B p6_B p6_L (by decide +kernel),by simp⟩
def p7_C : List (Nat × List Nat) := [(0,[])]
def p7_t : Tabs := (p7_C.map (mkCut true p7_Z),[(1,0),(2,0)],[],[[]])
theorem p7_W : TabsP true p7_R p7_T p7_t := ⟨cutsGood p7_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p7_D5 : List StD := [
([pw0,pw1,pw2,pw4,pw10],[0,1,5],[7,3,3,3,5,5,5,1,1,1])]
def p7_D4 : List StD := []
theorem p7_I4 : LevelN true p7_T 4 p7_D4 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p7_C5x0 : levelOK true p7_T p7_t 4 (p7_D4.map Prod.fst) ((p7_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p7_I5 : LevelN true p7_T 5 p7_D5 := levelStep p7_B p7_W p7_I4 (chunks 32 p7_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p7_C5x0
  ))
theorem p7_L : LowN true p7_R p7_T 6 := lowSearch p7_B p7_I5 (by decide +kernel)
def p8_T : Nat := 0xeac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8eac8
def p8_R : List Nat := [0, 1, 2, 3]
def p8_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,1,9)]
theorem p8_B : baseOK p8_T p8_R p8_E = true := by decide +kernel
def p8_Z : List SliceD := []
theorem p8_Y : ∀ s ∈ p8_Z, SliceN true p8_R p8_T s := by
  intro s h
  cases h
def p8_C : List (Nat × List Nat) := []
def p8_t : Tabs := (p8_C.map (mkCut true p8_Z),[(6,4),(3,1),(3,2),(9,12),(6,2),(9,1),(9,0),(6,12),(9,5)],[],[[]])
theorem p8_W : TabsP true p8_R p8_T p8_t := ⟨cutsGood p8_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p8_D3 : List StD := [
([pw0,pw1,pw2,pw4],[1,21,5,9,17,13,25,29,33],[5,56,74,5,131,274])]
def p8_D2 : List StD := []
theorem p8_I2 : LevelN true p8_T 2 p8_D2 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p8_C3x0 : levelOK true p8_T p8_t 2 (p8_D2.map Prod.fst) ((p8_D3.drop (0*32)).take 32) = true := by decide +kernel
theorem p8_I3 : LevelN true p8_T 3 p8_D3 := levelStep p8_B p8_W p8_I2 (chunks 32 p8_D3 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p8_C3x0
  ))
theorem p8_L : LowN true p8_R p8_T 4 := lowSearch p8_B p8_I3 (by decide +kernel)
def p9_T : Nat := 0xfeeafcc8feeafcc8feeafcc8feeafcc8feeafcc8feeafcc8feeafcc8feeafcc8
def p9_R : List Nat := [0, 1, 2, 3, 4]
def p9_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,2,10),(4,1,17)]
theorem p9_B : baseOK p9_T p9_R p9_E = true := by decide +kernel
def p9_Z : List SliceD := [(pw86,4,[1, 2, 3]),(pw6,4,[0, 1, 3, 4]),(pw3,4,[0, 1, 2, 4]),(pw10,5,[0, 1, 2, 3]),(pw7,5,[1, 2, 3, 0])]
theorem p9_Y : ∀ s ∈ p9_Z, SliceN true p9_R p9_T s := by
  unfold p9_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p9_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p9_B p8_B p8_L (by decide +kernel),mkSlice (w:=0) p9_B p8_B p8_L (by decide +kernel),mkSlice (w:=16) p9_B p6_B p6_L (by decide +kernel),mkSlice (w:=0) p9_B p2_B p2_L (by decide +kernel),by simp⟩
def p9_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[])]
def p9_t : Tabs := (p9_C.map (mkCut true p9_Z),[(3,2),(17,16),(21,20),(25,24),(12,8),(6,4),(6,2),(12,4),(10,8),(10,2),(7,4),(12,5),(3,5),(3,1),(6,20),(17,1),(6,18),(21,5),(17,9),(12,9),(6,0),(17,5),(11,8),(3,9),(10,24),(10,18),(25,9),(10,0),(12,20),(12,0),(12,1),(17,0),(10,16),(22,2),(7,0),(6,16),(12,16)],[],[[]])
theorem p9_W : TabsP true p9_R p9_T p9_t := ⟨cutsGood p9_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p9_D6 : List StD := [
([pw0,pw1,pw2,pw4,pw10],[0,1,12,3,4,8,5,17,25,29,9,13,21,33,37],[67,1027,2051,67,4504,25128,5,952,5,5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p9_D5 : List StD := [
([pw0,pw1,pw2,pw19,pw4,pw10],[1,37,21,61,9,25,29,8,5,17,41,45,49,53,57,65,69,73,3],[1029,17,257,2051,17,4132,8192,70,16396,512,66,32808,262274,65544,131082]),
([pw87,pw0,pw1,pw2,pw4,pw10],[5,29,61,1,17,37,21,12,16,25,45,53,57,73,77,81,85],[9,2048,512,34,388,9,16401,1027,9,32848,34,4164,34,65556,8198]),
([pw0,pw1,pw2,pw4,pw20,pw10],[1,25,33,61,13,17,37,4,5,29,53,77,85,89,93,97,101,105,3],[8197,2051,17,257,17,38,16452,1024,32780,34,262274,4106,512,65608,131080]),
([pw88,pw0,pw1,pw2,pw4,pw10],[5,17,61,1,25,29,33,12,16,37,45,53,73,77,85,97,109],[9,2048,18,512,388,9,8195,1057,9,18,65632,32836,18,16390,4132]),
([pw0,pw1,pw2,pw4,pw89,pw10],[21,1,61,29,53,4,9,17,69,25,33,45,57,77,113],[17,8322,2058,66,66,17,1025,17,4101,40,512,388,32,16396,260])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p9_D4 : List StD := [
([pw90,pw0,pw1,pw2,pw10],[1,25,37,69,109,61,117,41,45,53,121,125,129],[261,532,70,44,145,1027,2057,82,4120,42]),
([pw91,pw0,pw1,pw4,pw10],[1,25,37,61,81,117,53,77,121,125,133,137,141,145],[131,82,38,1034,2065,261,521,52,4120,8204])]
def p9_D3 : List StD := []
theorem p9_I3 : LevelN true p9_T 3 p9_D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p9_C4x0 : levelOK true p9_T p9_t 3 (p9_D3.map Prod.fst) ((p9_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p9_I4 : LevelN true p9_T 4 p9_D4 := levelStep p9_B p9_W p9_I3 (chunks 32 p9_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p9_C4x0
  ))
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
theorem p9_I6 : LevelN true p9_T 6 p9_D6 := levelStep p9_B p9_W p9_I5 (chunks 32 p9_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p9_C6x0
  ))
theorem p9_L : LowN true p9_R p9_T 7 := lowSearch p9_B p9_I6 (by decide +kernel)
def p10_T : Nat := 0xfeeefac0feeefac0feeefac0feeefac0feeefac0feeefac0feeefac0feeefac0
def p10_R : List Nat := [0, 1, 2, 3, 4]
def p10_E : List (Nat × Nat × Nat) := [(0,8,9),(1,4,6),(2,2,6),(3,1,9),(4,1,17)]
theorem p10_B : baseOK p10_T p10_R p10_E = true := by decide +kernel
def p10_Z : List SliceD := [(pw85,4,[1, 2, 3, 4]),(pw5,4,[0, 3, 2, 4]),(pw6,4,[0, 4, 1, 3]),(pw3,4,[1, 4, 0, 2]),(pw7,4,[2, 3, 0, 1])]
theorem p10_Y : ∀ s ∈ p10_Z, SliceN true p10_R p10_T s := by
  unfold p10_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p10_B p8_B p8_L (by decide +kernel),mkSlice (w:=0) p10_B p8_B p8_L (by decide +kernel),mkSlice (w:=0) p10_B p8_B p8_L (by decide +kernel),mkSlice (w:=0) p10_B p8_B p8_L (by decide +kernel),mkSlice (w:=0) p10_B p8_B p8_L (by decide +kernel),by simp⟩
def p10_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[])]
def p10_t : Tabs := (p10_C.map (mkCut true p10_Z),[(9,8),(11,10),(7,5),(21,20),(7,3),(9,1),(17,1),(12,8),(26,24),(11,3),(18,2),(12,4),(28,24),(21,5),(28,20),(26,10),(6,5),(6,3),(6,2),(6,4),(9,3),(17,5),(18,10),(7,4),(18,16),(12,5),(17,16),(18,3),(17,3),(7,2),(9,0),(17,0),(12,10),(9,10),(11,8),(14,8),(9,5),(12,20),(17,20),(21,16),(18,24),(26,16),(12,24),(12,0),(7,1),(12,16),(6,0),(6,1),(7,0),(11,2),(18,0),(18,8),(9,2),(17,2),(17,4)],[],[[]])
theorem p10_W : TabsP true p10_R p10_T p10_t := ⟨cutsGood p10_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p10_D6 : List StD := [
([pw0,pw1,pw2,pw4,pw10],[3,0,4,8,12,16,1,9,17,13,21,29,33,5,25,37,41,45,49,53,57,61],[8391,843,1619,16995,2445,37013,69797,133401,786729,3146801])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p10_D5 : List StD := [
([pw0,pw1,pw11,pw2,pw4,pw10],[25,45,73,5,9,21,29,41,16,1,65,69,77,81,85,89,3],[1048,512,2060,42,137,4096,84,8210,145,68,34,65793,38,16389,32771]),
([pw0,pw1,pw2,pw13,pw4,pw10],[21,41,77,13,17,25,45,97,12,1,65,69,73,81,85,89,93,3],[66564,2072,512,73,42,132,132,8197,38,4096,81,16402,131329,34,32771]),
([pw0,pw1,pw2,pw4,pw15,pw10],[25,73,77,21,41,1,9,17,29,45,61,81,85,101,105],[68,130,8232,16384,49,262,2060,68,21,258,130,4099,512,1033,17]),
([pw0,pw1,pw2,pw4,pw10,pw17],[45,73,77,21,25,9,17,1,29,41,57,81,85,105,109,113],[36,66,9,24592,128,262,2053,32788,36,11,4114,66,1025,9,512]),
([pw0,pw1,pw2,pw19,pw4,pw10],[25,45,73,77,1,37,41,5,21,29,53,65,69,89,93,97,117,121,125,129],[18440,69636,144,131090,262161,524300,32768,42,73,512,38,1029,258,65,8195]),
([pw0,pw1,pw2,pw4,pw20,pw10],[1,73,25,105,29,33,37,41,8,21,69,77,81,85,89,133,137,3],[98305,1027,9,9,9,18,4192,2048,164,18,131330,8198,512,16452,132]),
([pw0,pw1,pw2,pw4,pw10,pw92],[1,45,73,29,5,37,41,25,49,69,77,89,97,105,113,121],[17,517,32771,8193,17,12,34,20544,1024,14,260,12,2114,34,128]),
([pw0,pw1,pw2,pw4,pw89,pw10],[77,1,13,29,53,25,33,45,21,65,73,93,97,105,141,145,149],[2561,6,6,8194,6,16393,65,4097,65,32904,1024,56,256,65680,48]),
([pw0,pw1,pw2,pw4,pw10,pw21],[45,77,1,21,53,97,105,4,25,49,65,73,81,85,93,121,149,153,157,3],[17410,393220,32773,68,68,34,4099,34,524418,9,8720,2048,65553,9,256]),
([pw0,pw1,pw2,pw4,pw10,pw22],[73,77,29,105,1,61,97,0,21,25,57,65,69,89,93,117,161,165,169,3],[18434,36865,24,24,524424,7,196610,66,66,5,262177,5,9248,256,512])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p10_D4 : List StD := [
([pw27,pw0,pw1,pw2,pw4],[73,125,5,9,25,29,21,45,69,77,81],[6,536,49,208,6,259,6,41,1096,33]),
([pw33,pw0,pw1,pw2,pw10],[21,25,77,121,41,173,45,65,69,81,177,181],[73,517,65,19,140,296,26,1060,22,2082]),
([pw91,pw0,pw1,pw4,pw10],[41,73,185,25,173,29,1,69,81,117,181,189,193,197],[642,38,34,11,6148,8272,9,276,13,1041]),
([pw93,pw0,pw2,pw4,pw10],[45,77,185,21,201,1,29,65,85,93,97,105,189,193,205],[642,70,11,1026,12292,9,2080,13,276,16401]),
([pw58,pw1,pw2,pw4,pw10],[1,29,77,73,121,125,45,89,105,137,209,213,217],[517,11,81,257,14,1044,2084,10,4130,176])]
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_C5x0 : levelOK true p10_T p10_t 4 (p10_D4.map Prod.fst) ((p10_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p10_I5 : LevelN true p10_T 5 p10_D5 := levelStep p10_B p10_W p10_I4 (chunks 32 p10_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p10_C5x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_C6x0 : levelOK true p10_T p10_t 5 (p10_D5.map Prod.fst) ((p10_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p10_I6 : LevelN true p10_T 6 p10_D6 := levelStep p10_B p10_W p10_I5 (chunks 32 p10_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p10_C6x0
  ))
theorem p10_L : LowN true p10_R p10_T 7 := lowSearch p10_B p10_I6 (by decide +kernel)
def p11_T : Nat := 0xeeeaece0eeeaece0eeeaece0eeeaece0eeeaece0eeeaece0eeeaece0eeeaece0
def p11_R : List Nat := [0, 1, 2, 3, 4]
def p11_E : List (Nat × Nat × Nat) := [(0,4,5),(1,4,6),(2,1,5),(3,2,10),(4,1,17)]
theorem p11_B : baseOK p11_T p11_R p11_E = true := by decide +kernel
def p11_Z : List SliceD := []
theorem p11_Y : ∀ s ∈ p11_Z, SliceN true p11_R p11_T s := by
  intro s h
  cases h
def p11_C : List (Nat × List Nat) := []
def p11_t : Tabs := (p11_C.map (mkCut true p11_Z),[(5,4),(10,9),(6,4),(6,2),(5,0),(10,3),(10,2),(17,1),(17,0),(5,1),(10,0),(17,3),(5,9),(6,18),(17,9)],[],[[]])
theorem p11_W : TabsP true p11_R p11_T p11_t := ⟨cutsGood p11_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p11_D4 : List StD := [
([pw0,pw1,pw2,pw4,pw10],[1,9,13,25,29,5,17,21,33,37,41,45,49,53,57],[35,69,137,273,518,1034,2066,4108,8212,16408])]
def p11_D3 : List StD := []
theorem p11_I3 : LevelN true p11_T 3 p11_D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p11_C4x0 : levelOK true p11_T p11_t 3 (p11_D3.map Prod.fst) ((p11_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p11_I4 : LevelN true p11_T 4 p11_D4 := levelStep p11_B p11_W p11_I3 (chunks 32 p11_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p11_C4x0
  ))
theorem p11_L : LowN true p11_R p11_T 5 := lowSearch p11_B p11_I4 (by decide +kernel)
def p12_T : Nat := 0xfefefeeefefafc88fefefeeefefafc88fefefeeefefafc88fefefeeefefafc88
def p12_R : List Nat := [0, 1, 2, 3, 4, 5]
def p12_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,8,12),(3,2,10),(4,1,17),(5,1,33)]
theorem p12_B : baseOK p12_T p12_R p12_E = true := by decide +kernel
def p12_Z : List SliceD := [(pw6,6,[0, 1, 5, 3, 4]),(pw2,6,[3, 4, 0, 1, 5]),(pw3,7,[4, 0, 1, 5, 2]),(pw7,7,[3, 1, 0, 5, 2]),(pw83,7,[0, 2, 3, 1, 4]),(pw85,5,[1, 2, 3, 4, 5]),(pw5,5,[0, 2, 4, 3, 5])]
theorem p12_Y : ∀ s ∈ p12_Z, SliceN true p12_R p12_T s := by
  unfold p12_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p12_B p5_B p5_L (by decide +kernel),mkSlice (w:=4) p12_B p7_B p7_L (by decide +kernel),mkSlice (w:=0) p12_B p9_B p9_L (by decide +kernel),mkSlice (w:=0) p12_B p9_B p9_L (by decide +kernel),mkSlice (w:=0) p12_B p10_B p10_L (by decide +kernel),mkSlice (w:=0) p12_B p11_B p11_L (by decide +kernel),mkSlice (w:=0) p12_B p11_B p11_L (by decide +kernel),by simp⟩
def p12_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(2,[262]),(5,[]),(2,[263]),(2,[260]),(3,[260]),(4,[384]),(6,[]),(2,[261]),(4,[385]),(3,[261]),(3,[263]),(4,[386]),(3,[262]),(4,[387]),(2,[261,404])]
def p12_t : Tabs := (p12_C.map (mkCut true p12_Z),[(17,16),(10,8),(3,2),(3,1),(12,8),(13,9),(13,5),(10,2),(17,1),(20,4),(33,1),(34,2),(22,18),(22,6),(33,5),(17,9),(33,9),(34,18),(10,9),(37,36),(12,5),(38,36),(20,6),(12,4),(37,5),(7,6),(19,18),(7,5),(3,0),(3,9),(25,24),(26,24),(20,16),(44,40),(26,18),(25,9),(44,36),(41,9),(52,36),(50,18),(3,18),(33,0),(34,0),(3,5),(41,8),(11,9),(50,16)],[],[[]])
theorem p12_W : TabsP true p12_R p12_T p12_t := ⟨cutsGood p12_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p12_D8 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw84],[0,4,8,12,16,17,33,41,25,29,37,45,1,5,9,13,21,49,53,57,61,65,69,3],[8450048,65571,772,1096,2192,131107,772,262216,2192,39,1131,524467,1048588,2097172,4194328])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p12_D7 : List StD := [
([pw94,pw0,pw1,pw2,pw4,pw10,pw84],[24,32,36,40,44,3,20,1,5,77,85,0,4,28,29,33,37,41,61,65,69,73,81,89,93,97],[65,8193,6145,99,37,41,2097169,641,4194307,133,521,1296,274,8388628,1048,16793602,98308,33685512,262150,524298,1048588]),
([pw0,pw1,pw11,pw2,pw4,pw10,pw84],[24,44,48,52,9,13,33,56,21,25,41,29,45,49,53,0,4,17,37,61,65,69,73,93,97,101,105,109,3],[4194355,2,33554705,2581,67108945,5145,1,134225954,2598,16610,5162,229632,8389124,262336,268436488,2564,24896,16778504,524420,1048588,2097352]),
([pw12,pw0,pw1,pw2,pw4,pw10,pw84],[24,20,44,60,64,25,33,41,32,9,29,53,0,4,48,5,45,49,61,65,69,85,97,101,113],[260,16385,12289,291,73,145,16777733,8389121,35,73,145,2260996,1062,2124,65684,1058,2120,4194448,262154,524306,1048600]),
([pw95,pw0,pw1,pw2,pw4,pw10,pw84],[44,28,68,72,29,45,53,24,48,13,25,33,0,4,1,5,21,41,61,65,69,77,97,109,113],[257,32769,12289,275,69,41,16777857,2179200,1042,2116,131112,8389121,19,69,41,1042,2116,4194344,262150,524298,1048588])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p12_D6 : List StD := [
([pw0,pw1,pw2,pw96,pw10,pw84],[44,1,5,17,29,37,45,77,85,25,33,129,21,41,97,117,121,125,133,137,141,145,149,153,157],[32775,4234,66066,1186,8386,261,261,131077,261,2584,3112,278600,1572912,6291536,25165920]),
([pw0,pw1,pw2,pw4,pw97,pw84],[24,1,5,17,33,41,93,49,77,85,29,53,45,97,121,125,133,137,141,145,149,153,157,161],[8388615,259,16387,259,259,652,1604,34836,4644,1224,2200,73768,393296,1572960,6291504]),
([pw0,pw1,pw2,pw4,pw10,pw98],[24,44,1,5,29,33,41,77,85,129,17,37,73,93,97,121,125,133,137,141,145,149,153,157],[4111,133,32773,133,133,266,266,65546,266,9744,3616,148032,786480,3145808,12583008]),
([pw99,pw0,pw1,pw11,pw2,pw4,pw10],[21,29,33,9,45,37,93,17,13,41,76,25,53,61,73,165,169,173],[536,528,1024,145,82,52,16648,32768,137,2058,44,65536,131329,66,4100,129,66,36,67,37,8198]),
([pw99,pw0,pw1,pw2,pw4,pw10],[17,37,45,93,165,169,29,33,49,9,13,21,41,25,53,97,101,105,109,137,141,149,157,177,181,185],[4628,5156,34821,2097228,4194438,1584,67601,8396824,131218,262433,16777320,33570850,329,387,1572874])]
def p12_D5 : List StD := []
theorem p12_I5 : LevelN true p12_T 5 p12_D5 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p12_C6x0 : levelOK true p12_T p12_t 5 (p12_D5.map Prod.fst) ((p12_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p12_I6 : LevelN true p12_T 6 p12_D6 := levelStep p12_B p12_W p12_I5 (chunks 32 p12_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p12_C6x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p12_C7x0 : levelOK true p12_T p12_t 6 (p12_D6.map Prod.fst) ((p12_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p12_I7 : LevelN true p12_T 7 p12_D7 := levelStep p12_B p12_W p12_I6 (chunks 32 p12_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p12_C7x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p12_C8x0 : levelOK true p12_T p12_t 7 (p12_D7.map Prod.fst) ((p12_D8.drop (0*32)).take 32) = true := by decide +kernel
theorem p12_I8 : LevelN true p12_T 8 p12_D8 := levelStep p12_B p12_W p12_I7 (chunks 32 p12_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p12_C8x0
  ))
theorem p12_L : LowN true p12_R p12_T 9 := lowSearch p12_B p12_I8 (by decide +kernel)
def p13_T : Nat := 0xfeeefaeafeeefaeafeeefaeafeeefaeafeeefaeafeeefaeafeeefaeafeeefaea
def p13_R : List Nat := [0, 1, 2, 3, 4]
def p13_E : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6),(3,4,12),(4,2,18)]
theorem p13_B : baseOK p13_T p13_R p13_E = true := by decide +kernel
def p13_Z : List SliceD := []
theorem p13_Y : ∀ s ∈ p13_Z, SliceN true p13_R p13_T s := by
  intro s h
  cases h
def p13_C : List (Nat × List Nat) := []
def p13_t : Tabs := (p13_C.map (mkCut true p13_Z),[(1,0),(1,2),(3,0),(1,4),(5,0),(1,8),(9,0),(1,16),(17,0),(12,8),(6,2),(6,4),(18,24),(12,4),(18,2),(18,0),(12,24),(18,10)],[],[[]])
theorem p13_W : TabsP true p13_R p13_T p13_t := ⟨cutsGood p13_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p13_D4 : List StD := [
([pw0,pw1,pw2,pw4,pw10],[1,37,57,41,45,53,5,9,13,17,21,25,29,33,49,61,65,69],[193,769,3073,12289,10,16432,32788,10,65542,131108])]
def p13_D3 : List StD := []
theorem p13_I3 : LevelN true p13_T 3 p13_D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p13_C4x0 : levelOK true p13_T p13_t 3 (p13_D3.map Prod.fst) ((p13_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p13_I4 : LevelN true p13_T 4 p13_D4 := levelStep p13_B p13_W p13_I3 (chunks 32 p13_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p13_C4x0
  ))
theorem p13_L : LowN true p13_R p13_T 5 := lowSearch p13_B p13_I4 (by decide +kernel)
def p14_T : Nat := 0xfeeefaeafeccfac0feeefaeafeccfac0feeefaeafeccfac0feeefaeafeccfac0
def p14_R : List Nat := [0, 1, 2, 3, 4, 5]
def p14_E : List (Nat × Nat × Nat) := [(0,8,9),(1,4,6),(2,2,6),(3,1,9),(4,2,18),(5,1,33)]
theorem p14_B : baseOK p14_T p14_R p14_E = true := by decide +kernel
def p14_Z : List SliceD := [(pw83,5,[1, 3, 2, 0, 4]),(pw84,5,[0, 1, 2, 3, 4]),(pw7,5,[0, 2, 3, 1, 5]),(pw10,5,[1, 0, 3, 2, 5])]
theorem p14_Y : ∀ s ∈ p14_Z, SliceN true p14_R p14_T s := by
  unfold p14_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p14_B p11_B p11_L (by decide +kernel),mkSlice (w:=32) p14_B p13_B p13_L (by decide +kernel),mkSlice (w:=0) p14_B p11_B p11_L (by decide +kernel),mkSlice (w:=16) p14_B p13_B p13_L (by decide +kernel),by simp⟩
def p14_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[])]
def p14_t : Tabs := (p14_C.map (mkCut true p14_Z),[(9,8),(6,4),(11,10),(7,5),(6,2),(37,36),(7,3),(12,4),(9,1),(18,2),(25,24),(19,3),(33,1),(18,16),(12,8),(26,24),(11,3)],[],[[]])
theorem p14_W : TabsP true p14_R p14_T p14_t := ⟨cutsGood p14_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p14_D6 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw84],[0,4,1,5,17,29,37,8,12,21,33,57,9,13,25,41,45,49,53,61,65],[12300,16916,1572,98372,131079,264216,1572904,456,11,3120,464,19,480,35,67])]
def p14_D5 : List StD := []
theorem p14_I5 : LevelN true p14_T 5 p14_D5 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p14_C6x0 : levelOK true p14_T p14_t 5 (p14_D5.map Prod.fst) ((p14_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p14_I6 : LevelN true p14_T 6 p14_D6 := levelStep p14_B p14_W p14_I5 (chunks 32 p14_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p14_C6x0
  ))
theorem p14_L : LowN true p14_R p14_T 7 := lowSearch p14_B p14_I6 (by decide +kernel)
def p15_T : Nat := 0xfffffffffffffff8fffefafaffcc8888fffffffffffffff8fffefafaffcc8888
def p15_R : List Nat := [0, 1, 2, 3, 4, 5, 6]
def p15_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,32,36),(3,16,24),(4,2,18),(5,1,33),(6,4,68)]
theorem p15_B : baseOK p15_T p15_R p15_E = true := by decide +kernel
def p15_Z : List SliceD := [(pw85,9,[4, 6, 5, 2, 3, 1]),(pw100,8,[6, 3, 5, 2, 4]),(pw3,9,[5, 6, 1, 4, 0, 2]),(pw101,7,[1, 4, 3, 6, 0]),(pw6,9,[4, 6, 0, 5, 1, 3]),(pw102,7,[0, 5, 2, 6, 1]),(pw103,7,[4, 5, 0, 1, 2, 3]),(pw104,4,[0, 5, 2, 1]),(pw105,4,[1, 4, 3, 0]),(pw106,5,[1, 3, 4, 6]),(pw107,5,[0, 2, 5, 6]),(pw108,4,[0, 5, 2, 1]),(pw109,4,[1, 4, 3, 0])]
theorem p15_Y : ∀ s ∈ p15_Z, SliceN true p15_R p15_T s := by
  unfold p15_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p15_B p4_B p4_L (by decide +kernel),mkSlice (w:=0) p15_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p15_B p12_B p12_L (by decide +kernel),mkSlice (w:=0) p15_B p9_B p9_L (by decide +kernel),mkSlice (w:=0) p15_B p12_B p12_L (by decide +kernel),mkSlice (w:=0) p15_B p9_B p9_L (by decide +kernel),mkSlice (w:=0) p15_B p14_B p14_L (by decide +kernel),mkSlice (w:=0) p15_B p8_B p8_L (by decide +kernel),mkSlice (w:=0) p15_B p8_B p8_L (by decide +kernel),mkSlice (w:=1) p15_B p6_B p6_L (by decide +kernel),mkSlice (w:=2) p15_B p6_B p6_L (by decide +kernel),mkSlice (w:=8) p15_B p8_B p8_L (by decide +kernel),mkSlice (w:=4) p15_B p8_B p8_L (by decide +kernel),by simp⟩
def p15_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(0,[257]),(1,[521]),(6,[]),(0,[129]),(1,[513]),(4,[129]),(3,[389]),(7,[]),(0,[131]),(1,[514]),(4,[131]),(0,[261]),(5,[389]),(1,[257]),(2,[129]),(8,[]),(0,[262]),(1,[258]),(2,[131]),(0,[257,129]),(1,[521,513]),(0,[257,261]),(1,[521,257]),(9,[]),(10,[]),(0,[257,154]),(3,[391]),(5,[391]),(0,[129,281]),(1,[257,533]),(0,[257,130]),(0,[257,152]),(1,[521,22]),(3,[390]),(5,[390]),(6,[642]),(0,[129,538]),(1,[513,647]),(4,[129,791]),(3,[389,278]),(1,[513,150]),(4,[129,666]),(11,[]),(0,[129,282]),(1,[513,278]),(0,[131,281]),(1,[514,277]),(0,[261,783]),(1,[257,406]),(2,[129,791]),(5,[389,278]),(0,[261,410]),(2,[129,666]),(12,[]),(0,[261,26]),(1,[257,534]),(0,[262,25]),(1,[258,533]),(0,[261,260,29]),(0,[129,128,285]),(5,[389,276])]
def p15_t : Tabs := (p15_C.map (mkCut true p15_Z),[(3,2),(33,32),(7,6),(11,10),(49,48),(67,66),(7,5),(3,1),(11,9),(18,16),(50,48),(67,65),(28,20),(24,16),(36,32),(52,48),(68,64),(72,64),(56,48),(33,1),(50,34),(49,17),(80,64),(80,16),(96,64),(96,32),(38,34),(74,66),(56,40),(18,48),(24,20),(36,48),(52,16),(24,48),(80,48),(68,4),(112,48),(3,6),(3,10),(24,9),(3,5),(3,9),(3,17),(18,6),(18,10),(18,2),(44,40),(24,8),(36,6),(33,9),(69,65),(25,17),(52,20),(81,65),(81,17),(56,32),(18,66),(98,66),(98,34),(33,65),(7,2),(11,2),(33,48),(49,32),(3,66),(67,2),(7,1),(11,1),(3,65),(67,1),(28,16),(33,17),(36,4),(82,66),(38,6),(24,0),(104,32),(3,0),(33,5),(25,9),(97,65),(22,6),(36,0),(68,0),(84,16),(25,16),(24,32),(72,0),(49,65),(80,32),(80,17),(80,20),(22,66),(24,64),(38,32),(44,32),(36,16),(96,34),(36,64),(96,40),(41,65),(72,8),(22,2),(41,1),(80,0),(96,0),(29,9),(69,1),(38,2),(70,2),(44,8),(76,8),(25,1),(44,4),(73,1),(46,6),(74,2),(28,4),(76,4),(72,32),(56,16),(24,1),(24,4),(28,0),(36,2),(36,8),(37,1),(68,16),(52,32),(68,8),(26,2),(44,0),(28,1),(44,2),(76,0),(25,20),(38,40),(36,40)],[],[[]])
theorem p15_W : TabsP true p15_R p15_T p15_t := ⟨cutsGood p15_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p15_D10 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw84,pw110],[0,1,4,12,25,8,49,16,57,3,20,5,65,69,77,81,9,13,17,21,29,33,37,41,45,53,61,73,85,89,93,97,101],[2051,65539,131075,262147,2051,524291,1048596,2097172,4194324,8388628,16777236,33554528,67109256,4488,4488,8288,134217824,8288,268486152,1610647040,6442467848])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p15_D9 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw84,pw111,pw110],[12,20,24,1,53,105,109,28,5,3,37,65,81,85,93,32,9,13,17,21,29,45,57,113,117,121,125,129,133,137,141],[268,65548,131084,262156,268,268,524300,4194337,82,8392706,16777345,1049728,2098304,33554435,67108867,134225953,2081,2081,82,268435459,82,82,3,1,20994,3,536879617,1073791488]),
([pw0,pw1,pw2,pw4,pw10,pw84,pw110,pw112],[20,36,1,40,25,49,44,61,3,32,48,5,17,37,65,69,85,93,52,9,13,21,29,33,41,45,53,57,73,77,89,97,145],[2054,524294,1048582,4102,2054,2097158,4102,4194328,8388632,8216,16777240,33554456,8216,67108897,193,16576,16576,134217920,32801,268435489,32801,289,1073807617,131585,513,6442583808,537199872,1]),
([pw113,pw0,pw1,pw2,pw4,pw10,pw84,pw110],[20,32,56,60,64,21,45,69,65,1,93,181,12,5,41,57,73,81,89,97,121,145,149,153,157,161,165,169,173,177,3],[548,74,274,131,262147,1074270210,3,108,4194324,8388613,16777221,8228,548,33554456,67108873,134217737,16456,74,1048593,268435473,33040,274,536873089,65665,131,133121,1027,2098178]),
([pw0,pw1,pw2,pw4,pw10,pw84,pw110,pw114],[12,72,68,1,105,76,33,53,3,32,80,5,69,181,41,65,81,145,84,9,13,17,21,29,37,45,57,61,73,89,185,189],[2060,524300,1048588,2097164,2060,4194316,2060,67108881,8388834,16777314,16417,33554528,16480,1073741841,134217745,32785,32785,273,2147496066,268436481,5250,5250,65795,537010946,336130,131585,513,1]),
([pw115,pw0,pw1,pw2,pw4,pw10,pw84,pw110],[12,32,88,92,96,21,45,65,69,1,17,61,145,20,37,53,77,85,89,97,101,121,149,153,161,165,193,197,3],[548,74,131,274,268705794,524291,3,108,4194309,8388628,1060,1029,548,16777225,33554456,16456,67108873,74,2097169,2177,2177,131,33040,134217745,274,196609,1052674,4099])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p15_D8 : List StD := [
([pw0,pw1,pw2,pw4,pw84,pw111,pw110,pw112],[48,5,37,53,57,20,93,209,89,201,104,81,52,1,29,109,3,21,85,100,9,13,25,33,41,45,49,105,133,137,185,205,213,217,221,225],[24582,1049106,2149580810,270466,4294975746,8590065730,657410,138412052,8421388,16778372,17668,33555524,17412,1140850712,262800,785,593,2577,268435625,33064,32872,17179934760,32,536936641,6273,34359808320,6145,32]),
([pw0,pw1,pw2,pw4,pw10,pw111,pw110,pw114],[5,37,53,57,12,72,81,109,137,108,85,97,84,1,29,201,3,45,113,233,112,9,13,17,21,25,33,49,61,105,129,185,205,229,237],[24579,2129929,4299161605,8389185,8705,16777729,8705,570425354,67108998,278594,8589953026,655618,1180674,2281701388,268435544,34840,33048,1073807384,262340,2212,420,1188,16,590176,5216,17179941120,5152,16]),
([pw0,pw1,pw2,pw4,pw10,pw84,pw116,pw111,pw110],[37,1,53,57,85,3,116,120,81,29,141,5,65,69,24,28,32,124,77,93,117,121,125,129,133,149,153,161,165,181,221,241,245,249,253,257,261,265,269,273,277,281,285],[513,2181038082,4362076162,25769803778,2050,16450,2050,103079215106,137573171201,275146342401,513,1048593,32897,513,1649267441665,2199025352708,4194568,8388632,104,4104,4104,1073742084,16777236,164,8196,8196,4398046511376,192,536870912,1312,192,262144,1072,131072,524288,66592]),
([pw0,pw1,pw2,pw4,pw10,pw84,pw111,pw110,pw117],[37,1,53,57,85,29,81,5,93,3,128,65,69,101,12,20,132,21,45,89,97,117,121,125,129,133,141,149,153,161,165,221,241,245,249,253,265,269,281,285],[33,4429185026,8858370050,51539607554,130,130,131074,130,69256347649,138512695297,33,2097169,33,262145,33,274882101252,8388680,16777240,2056,2056,16904,2147483716,33554452,4100,4100,33284,549755813968,524288,8512,1024,1048576,8464,65536,768,1024,67108864]),
([pw0,pw1,pw2,pw4,pw10,pw84,pw110,pw117],[5,37,53,57,81,93,209,48,213,72,1,29,109,201,229,233,3,85,0,4,52,84,124,136,140,9,13,17,21,25,33,41,45,49,61,105,113,133,185,205,217],[3075,33562633,549822922757,134218001,132161,1099780063265,8651777,34896609290,1073745926,2322,2147500098,4295000098,17303554,283467841548,17179869336,139336,8360,65672,68719480852,137438954180,4644,66052,16720,33072,2097152,49248,1048576,4259840]),
([pw118,pw0,pw1,pw2,pw4,pw10,pw84,pw111,pw110],[1,65,69,29,81,85,5,53,57,37,141,3,12,20,144,148,89,93,97,117,121,125,133,149,153,161,165,249,257,261,273,277,285],[65,520,258,132,20496,12320,32768,131072,65,8388611,16777221,134217745,65,65,805306369,33554442,67108876,520,524328,520,3221225480,1048582,2097170,258,258,258,132,4194340,132,132,4294967344,65536,3088,262144,3104,3072]),
([pw118,pw0,pw1,pw2,pw4,pw10,pw84,pw110],[156,160,124,1,152,29,65,5,53,57,69,12,20,37,0,4,136,21,45,81,85,89,97,117,121,125,133,149,153,161,165,249,3],[16524,41008,2625,5378,4099,2051,4295032832,140,134217741,268435470,2147483662,140,131084,536870961,1073741874,8240,8388657,262192,16777283,33554499,577,577,1282,67108867,1282,7,2621442,5242881]),
([pw119,pw0,pw1,pw2,pw4,pw10,pw84,pw111,pw110],[1,29,53,57,65,69,85,37,81,93,48,5,21,45,101,32,72,77,117,121,125,133,141,149,153,161,165,181,249,253,285,3],[4097,8194,24,36,1024,65536,1024,4194304,131,8388617,16777221,805306369,2049,2049,4097,33554442,67108870,130,262210,130,8194,524300,1048840,24,24,24,36,2097220,36,36,1073742144,134217728,17152,131072,16960,2147516928]),
([pw120,pw0,pw1,pw2,pw10,pw84,pw110,pw112],[20,1,29,57,53,77,93,164,17,89,176,37,61,85,201,172,109,289,3,52,168,180,9,21,25,41,45,49,73,97,105,145,205,213,217,293,297],[4294967570,67604,134221848,66177,268443696,17,1,2310,4210698,8589935107,131362,17188257858,1048834,1090519052,34359738885,68753031204,67141700,34820,5129,147496,17480,5128,270849,193,128,2684354752,2891808,1]),
([pw120,pw0,pw1,pw2,pw10,pw84,pw110],[168,180,188,184,17,20,1,37,57,52,29,61,65,77,89,301,3,21,41,45,73,85,97,149,161,221,305],[81,1160,2310,49184,3219970,32,81,8388613,81,81,131089,16777228,1160,262280,524424,2310,4358,4358,33570850,32801,71377410]),
([pw0,pw1,pw2,pw4,pw10,pw84,pw110,pw112,pw114],[37,48,72,1,53,57,17,29,69,3,52,41,61,65,145,84,21,45,73,121,149,153,161,165,181,241,245,265,269,281],[129,34603016,69206024,72,72,65544,72,72,138412033,276824065,129,2049,131073,129,2049,537395216,4128,8224,8224,4128,546,272,262160,272,532,272,518,16388,16777216,32774,16386,1030,1024,4,2,6]),
([pw0,pw1,pw2,pw4,pw10,pw84,pw110,pw112,pw117],[37,1,72,53,48,57,85,17,29,192,61,69,3,84,160,21,45,65,81,93,117,121,129,133,149,153,161,165,241,245,265,269,281],[257,285212674,570425346,130,130,32770,130,130,1140850689,2281701377,257,1048641,65537,257,257,4297064456,1056,4194400,131104,1056,4144,2056,8388680,2056,4108,524,84,524292,262144,8192,84,528,512,4,16384,16]),
([pw121,pw0,pw1,pw2,pw4,pw10,pw84,pw110],[52,48,196,200,1,73,65,81,21,37,77,0,45,53,69,85,89,101,121,125,141,149,153,161,165,181,193,221,249,309,313],[2324,521,67,8225,33554435,32771,1048579,536870940,2097174,4194325,268435477,1046,276,8388618,16777225,521,67108874,4105,262147,524291,1073742914,67,134217889,35,16417,131,65669,131075]),
([pw0,pw1,pw2,pw4,pw10,pw84,pw122,pw110],[84,128,72,5,37,53,57,181,97,109,1,201,317,204,208,29,41,81,0,4,9,13,17,21,25,33,45,49,61,73,77,93,101,105,185,205,229,321,325,3],[33816,1050696,34361835560,4198536,137438954760,271368,8396808,8606711888,33554992,37008,68719542544,606224,67125264,17314087008,275146342592,2370,549755813955,2114,4768,536871206,549,549,131462,131207,2147483781,1073741825,4294967555,7]),
([pw123,pw0,pw1,pw4,pw10,pw84,pw110,pw114],[84,12,1,29,53,181,57,41,97,220,5,73,81,109,233,317,212,201,3,216,224,13,17,21,33,61,101,105,145,185,205,229,321,329],[132164,134217928,536873040,33558624,131395,66,2,1164,1075838996,4227108,4294967558,8454149,66565,16785432,32936,2147483914,67125257,524425,41008,2578,8721,2577,266530,268451873,1314849,16387,8589934593,2]),
([pw123,pw0,pw1,pw4,pw10,pw84,pw110],[84,228,232,216,5,57,41,73,224,1,29,329,53,65,69,81,97,101,333,3,12,17,21,45,61,89,129,153,165,337],[530,1129,4261,17334561,75809,401441,530,134217734,2097170,530,4194322,268435468,1096,1097,8388681,16516,4229,16517,68159745,570982657,460803]),
([pw0,pw1,pw2,pw4,pw10,pw84,pw110,pw114,pw117],[37,1,48,53,57,81,72,236,5,29,41,65,73,3,52,156,21,45,69,85,101,121,125,149,153,161,165,221,241,245,249,253,265,269,281],[513,276824066,553648130,3221225474,258,65538,258,258,4328521729,8657043457,513,1025,131073,1025,513,17181966344,4194352,2064,2064,8212,148,134217768,4104,262152,4104,8264,36,100,160,128,1048580,524288,16384,4,32768,64]),
([pw124,pw0,pw1,pw2,pw4,pw10,pw84,pw110],[72,128,240,1,84,244,29,61,5,53,69,85,12,20,45,57,0,4,21,65,77,81,93,117,121,129,133,149,153,157,161,165,169],[65804,147552,36994,9729,2097169,1052691,8195,268,134217742,268435469,536870925,268,262172,1073741922,2147483745,4294967393,8388706,16480,16777347,32898,33556610,524434,1537,67108867,1537,2051,4194321,2070]),
([pw0,pw1,pw2,pw4,pw10,pw125,pw84,pw110],[48,132,5,37,53,57,89,52,201,248,252,29,109,1,17,85,0,4,9,13,21,25,33,41,45,49,61,93,105,137,181,185,197,205,213,293,3],[10252,262436,8590458900,17179885636,82436,8708,1049092,270532648,4198424,34359740488,134152,8389640,16778248,2181038128,67108961,289,289,289,4178,68719476882,4294967315,4114,1073741952,32835,134217922,32897,3,536871041])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p15_D7 : List StD := [
([pw120,pw0,pw1,pw2,pw84,pw111,pw110,pw112],[1,37,53,85,29,57,65,5,21,69,93,221,180,45,77,81,89,117,121,129,133,137,149,161,225,241,265,281,341,345,349],[268435461,22,134479876,1048588,516,516,32768,19,37748737,137,129,257,257,75497474,131082,18,8194,18,524328,96,96,96,16384,2098184,536872968,16843776,6144,1073741824]),
([pw0,pw1,pw2,pw4,pw111,pw110,pw112,pw114],[37,1,53,65,29,57,69,81,85,89,5,21,45,256,260,93,121,129,137,149,153,161,165,221,241,245,265,269,281,285,353,357],[17,17301506,34603010,1026,2050,2050,1026,69206017,138412033,17,4097,17,4097,268500996,40,40,40,131336,68,68,8388740,68,1074004480,8832,17152,2147483648,32768,536871296]),
([pw0,pw1,pw2,pw4,pw84,pw116,pw111,pw112],[37,1,53,93,57,81,85,29,225,120,5,77,89,101,117,121,125,129,133,141,149,153,161,165,221,241,245,249,253,265,269,281,285,361,365,369,373,3],[129,34603010,69206018,1026,8589934602,1026,402653186,541065217,1082130433,16449,521,129,129,2147516420,131152,17179869208,34359738640,65584,262212,137438953484,68719476996,16777252,520,2048,4294967392,4096,8192,524576]),
([pw118,pw0,pw1,pw2,pw4,pw84,pw111,pw112],[1,65,69,29,141,5,57,85,37,81,53,93,97,117,121,133,137,149,153,161,165,221,225,249],[33,264,66,1028,67712,4194304,2576,33,131075,262149,33,33,8388625,524298,1048588,8328,264,264,16390,66,66,66,32900,1028,2097172,4096,656,528]),
([pw123,pw0,pw1,pw4,pw10,pw111,pw110,pw114],[1,53,29,81,57,5,69,37,45,65,129,137,224,21,85,97,125,153,165,181,221,237,249,333,357,377,381,385],[33,33554452,67108882,65560,528,528,16384,33,131075,4194313,33,8193,33,262150,140,132,260,260,1048586,66,66,66,524288,16779272,134218760,2131968,5120,8388608]),
([pw0,pw1,pw2,pw4,pw10,pw116,pw111,pw114],[37,1,53,85,57,81,116,29,137,5,237,93,97,117,121,125,129,133,141,149,153,161,165,181,221,241,245,249,253,265,269,281,285,357,389,393,397,401,3],[129,34078722,68157442,402653186,322,514,514,538968065,1077936129,129,17179869441,129,8201,2147500036,32816,274877907024,34359739408,65560,16777252,68719476996,137438954500,131084,8589934688,8388608,4294967336,4096,2048,262152]),
([pw118,pw0,pw1,pw2,pw4,pw10,pw111,pw114],[1,65,69,29,141,5,53,81,85,37,57,137,89,117,121,125,149,153,161,165,237,249,357],[33,520,1026,68,4196480,1048576,2320,33,65539,131077,2097281,33,33,262154,524300,520,520,8216,16390,32898,1026,274,68,68,68,4096,400,272]),
([pw0,pw1,pw4,pw10,pw84,pw111,pw126,pw110],[37,1,53,85,57,81,365,29,5,65,69,141,77,117,121,125,129,133,149,153,161,165,181,221,241,245,249,253,257,261,265,269,273,277,281,285,3],[129,34078722,201326594,258,258,17039362,805306370,2149580801,129,8201,129,1074790401,12884901889,8388644,131084,1028,17179885572,1028,34359738408,4194304,32816,2144,4096,65560,68719476808,528,2112,592]),
([pw0,pw1,pw2,pw10,pw84,pw111,pw127,pw110],[37,1,53,57,85,81,141,29,397,5,65,69,77,117,121,125,129,133,149,153,161,165,181,221,241,245,249,253,257,261,265,269,273,277,285,3],[129,17039362,201326594,514,514,34078722,805306370,1074790401,129,8209,129,2149580801,12884901889,32808,65560,1032,16396,1032,17179869232,4194304,8388644,34359738464,4096,131092,336,2052,320,324]),
([pw0,pw1,pw2,pw4,pw10,pw84,pw116,pw117],[37,1,93,53,85,57,81,29,5,405,77,89,117,121,125,129,133,137,141,149,153,161,165,181,221,241,245,249,253,265,269,281,285,333,361,365,389,397,3],[129,34078722,68157442,402653186,258,17179869190,258,538968065,1077936129,129,4113,68719476741,129,2147491848,16480,32816,34359738404,8589935136,16777288,65560,137438953484,262664,4294967376,2116,8388608,131092,1024,274877906944]),
([pw128,pw0,pw1,pw4,pw10,pw84,pw111,pw110],[1,29,81,85,5,53,57,37,93,65,69,333,21,45,117,121,125,129,133,137,153,165,221,245,249,269,281,285,329,409],[17,130,67141632,65604,131144,576,576,17,9437185,16777221,17,17,4097,35651586,130,16394,130,8194,4194340,262184,1056,1056,134217740,536870912,2308,268435456,524552,2304]),
([pw129,pw0,pw1,pw2,pw10,pw84,pw111,pw110],[1,37,53,85,81,29,57,93,5,65,69,349,21,45,117,121,125,129,133,137,149,161,221,241,249,265,281,285,301,341,413],[536870917,38,67141636,4194324,262156,1028,1028,35,9437185,16777233,265,257,4097,35651586,34,16394,34,8194,65616,131144,576,576,134217752,268435456,2192,1073741824,524424,2176]),
([pw118,pw0,pw1,pw2,pw4,pw10,pw84,pw117],[1,65,69,29,5,89,37,85,53,57,81,405,0,93,117,121,125,133,141,149,153,161,165,237,249,333,417,421],[17,72,514,260,1056,8396928,4096,17,524291,1048581,16777249,17,17,2097162,4194316,72,16520,72,32774,65570,514,33556482,260,131204,264196,1056,67108864,134217728]),
([pw128,pw0,pw1,pw4,pw10,pw84,pw110,pw117],[1,29,81,85,224,5,53,37,57,264,21,45,65,69,93,117,121,125,129,133,153,165,221,225,245,249,269,281,329,333,409,3],[33,130,134283264,131332,262408,4352,512,33,17825793,33554437,33,1025,33,69206018,130,32778,2050,130,4194372,524360,8256,2147483728,28,8388628,1073741824,16408,268435456,536870912]),
([pw128,pw0,pw1,pw4,pw10,pw84,pw110],[1,29,49,57,329,333,409,5,37,85,109,201,425,81,93,13,17,21,33,41,45,53,61,73,89,97,101,105,185,205,429,433,437,441,445],[2185,134217994,270532620,4202568,2584,18472,387,536903685,69697,657,1073872929,263174,4418,2148007954,4296015906,5188,8598323220,17179870244,8784,16793696,100663344]),
([pw129,pw0,pw1,pw2,pw10,pw84,pw110,pw117],[1,37,53,81,85,180,29,57,5,20,21,45,65,69,89,117,121,125,129,133,149,161,221,237,241,249,265,281,301,341,349,413,3],[536870917,70,134283268,4194316,524308,8196,512,67,17825793,33554441,273,1025,257,69206018,66,32786,2050,66,131208,262288,4224,4294967456,40,16424,268435456,8388656,2147483648,1073741824]),
([pw129,pw0,pw1,pw2,pw10,pw84,pw110],[1,29,53,185,301,349,413,5,37,81,109,201,85,93,453,9,17,21,25,41,45,49,57,61,73,89,97,101,105,205,449,457,461,465,469,473],[536871045,1286,6291468,1556,16781380,9252,387,34825,1073807377,16577,2147614753,268697610,786,4295491650,8590983202,17188257816,18504,34359740456,4688,33562672,201326688]),
([pw118,pw119,pw0,pw1,pw2,pw4,pw10,pw84],[1,65,69,29,417,5,53,57,85,37,81,77,89,93,97,117,121,125,133,149,153,161,165,249,257,261,273,277,3],[268435456,33,520,130,68,1040,10496,50331649,201326600,130,68,4096,16384,33,524291,1048581,8388625,33,2097162,4194316,520,33032,65542,131090,130,68,262404,1040]),
([pw120,pw0,pw1,pw2,pw10,pw84,pw110,pw117],[1,37,53,85,180,29,61,221,17,160,21,45,57,65,69,77,81,89,117,121,129,133,149,161,241,265,281,301,341,477,3],[268435461,38,67633156,65668,2097164,16388,512,35,20971521,257,265,1025,257,41943042,34,262154,2050,34,4288,1048648,8256,1073741904,144,131216,134217728,536870936,32768,512]),
([pw120,pw0,pw1,pw2,pw10,pw84,pw130,pw110],[1,57,29,17,85,93,301,37,73,349,61,221,180,21,45,53,65,77,81,117,129,137,149,161,481,3],[9,132,1026,262464,16777488,32768,800,9,4194307,9,9,9,8193,8388614,132,524308,132,16388,1026,1048594,33558530,65538,2128,2112,608,131072,2097200,544]),
([pw120,pw0,pw1,pw2,pw10,pw84,pw110,pw114],[1,37,53,301,180,29,65,5,41,57,73,221,21,45,69,77,89,121,149,161,181,241,265,281,305,341,485,489,493,3],[33554437,38,8519684,1048588,1028,16388,1028,35,2359297,67108873,129,4097,129,4718594,34,258,8194,258,402653192,576,576,536870992,2056,65560,2072,16777232,32768,16]),
([pw123,pw0,pw1,pw4,pw10,pw84,pw110,pw112],[1,53,29,57,329,224,5,17,37,61,69,129,337,21,45,65,77,153,165,181,377,381,497,501,3],[65,1048588,2097162,520,65560,32776,520,65,131075,129,65,8193,129,262150,260,4194324,16388,260,1026,8388626,1026,16777250,2064,4128,524288,4144,2096,32]),
([pw128,pw0,pw1,pw4,pw10,pw84,pw110,pw112],[1,29,329,224,57,69,5,37,17,53,61,85,93,21,45,65,77,121,153,165,245,269,281,409,497,501,3],[65,130,4325376,1040,65556,32784,1040,65,1310721,257,65,8193,257,2621442,130,16777222,16386,130,544,33554468,544,67108904,2052,4104,8388608,4108,2060,8]),
([pw131,pw0,pw1,pw4,pw10,pw84,pw110],[1,29,53,57,181,329,333,41,5,109,201,317,73,81,97,101,84,13,17,21,33,45,61,93,105,129,185,205,429,433,437,441,445,505],[1289,16777354,67112972,4202520,17448,33864,387,134348805,264209,8589934881,268959809,1049094,2194,536871074,1075839042,2580,2147487780,4294967876,33562672,8454224,49248]),
([pw123,pw0,pw1,pw4,pw10,pw84,pw110,pw117],[1,53,29,81,57,224,5,129,37,264,21,41,45,65,69,73,85,125,153,165,181,221,249,329,333,337,377,381,509,3],[65,67108884,134217746,131096,65680,8208,512,65,262147,4194313,65,1025,65,524294,268,2052,4100,260,2097162,32770,16386,536870946,168,268435496,1048576,33554592,8388608,16777216]),
([pw123,pw0,pw1,pw4,pw10,pw132,pw84,pw110],[1,53,29,81,5,41,101,329,61,333,73,129,224,21,45,57,85,89,153,165,181,221,249,513,517,3],[17,36,1026,8388872,32768,65920,832,17,262147,4194313,17,17,8193,524294,36,36,36,16388,2097162,33558530,1026,16777282,1048576,2184,131080,2176,576,704]),
([pw129,pw0,pw1,pw2,pw10,pw84,pw110,pw114],[1,37,53,301,180,29,65,5,41,57,73,81,21,45,69,89,101,121,149,161,181,241,265,281,341,413,485,489,493,3],[16777221,38,8519684,1048588,1028,16388,1028,35,2359297,67108873,129,4097,129,4718594,34,258,8194,258,402653192,576,576,536870992,2056,32792,2072,65552,33554432,16]),
([pw133,pw0,pw1,pw2,pw10,pw84,pw110],[1,29,53,57,77,301,349,17,37,109,201,61,85,89,93,289,52,9,21,25,41,45,49,73,101,105,205,221,297,449,457,465,469,473,521],[67108997,774,4196364,8740,8392724,16964,387,132105,536871073,32913,1074004033,34078730,17179869474,269484050,2149580866,4294969384,33816,8589935688,134221872,24672,16842832])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p15_D6 : List StD := [
([pw0,pw1,pw2,pw84,pw111,pw127,pw112],[37,1,53,57,81,85,29,225,5,77,117,121,125,129,133,141,149,153,161,165,221,241,245,249,253,265,269,285,369,373],[65,2162690,258,258,4325378,25165826,33816577,1057,65,67633153,65,8232,268435592,2060,4120,512,16420,134217776,536871044,32912,1048596]),
([pw0,pw1,pw4,pw10,pw111,pw126,pw114],[37,1,85,53,29,57,81,5,141,237,117,121,125,133,149,153,161,165,181,221,241,245,249,253,265,269,281,285,393,401],[17,2129922,12582914,130,1064962,130,33685505,17,17,16842753,1029,524360,536871432,67110920,8204,262144,4192,134217796,268436000,260,292]),
([pw134,pw0,pw1,pw2,pw4,pw10,pw84],[1,57,29,81,85,405,5,53,37,77,117,121,125,129,133,141,149,153,161,165,181,221,245,249,269,285,333],[65,260,67108898,32800,1048616,560,65,65539,4325377,8388617,65,262150,17301508,260,1044,2178,4106,8210,2097288,16528,33554456]),
([pw129,pw128,pw0,pw1,pw10,pw84,pw110],[1,37,53,85,493,29,5,81,537,21,45,57,65,69,121,225,237,281,329,341,409,525,529,533],[147460,524293,38,1048596,262156,8196,65,34,144,2097160,6144,35,4194321,73,513,34,8388618,1026,152,33040,65800]),
([pw120,pw128,pw0,pw1,pw10,pw84,pw110],[1,37,53,85,493,29,329,61,537,5,21,45,65,69,121,225,281,301,341,409,477,497,529],[81924,262149,38,524308,76,8196,513,34,131216,72,4224,35,4194321,73,1025,34,2097162,2050,88,33040,1048840]),
([pw120,pw135,pw0,pw1,pw10,pw84,pw110],[1,37,61,85,121,301,29,93,329,5,21,45,53,57,65,137,333,349,409,485,497,541],[4116,2097169,82,262192,280,65680,517,70,8228,268,16516,67,524321,265,1025,66,1048586,2050,296,131232,32904]),
([pw120,pw123,pw0,pw1,pw10,pw84,pw110],[1,37,53,61,129,301,29,5,57,329,537,21,45,65,69,77,181,341,377,477,485,497,509],[268,131077,70,65572,532,16388,137,262154,264,32792,8200,67,1048609,129,2049,66,2097170,4098,560,4195360,525328]),
([pw129,pw123,pw0,pw1,pw10,pw84,pw110],[1,37,53,57,129,301,29,5,81,537,21,45,65,69,181,237,329,341,377,381,413,485,509,533],[524300,131077,70,16420,65556,8196,137,262154,296,1048600,4104,67,2097185,129,1025,66,8388626,2050,304,4194848,33296]),
([pw136,pw123,pw0,pw1,pw10,pw84,pw110],[1,37,53,61,129,301,29,5,101,329,333,21,45,57,69,89,181,341,413,485,497,545,549],[8204,131077,70,65572,532,16388,137,2097162,4194344,262168,1288,67,524321,129,2049,66,1048594,4098,560,32800,1296])]
def p15_D5 : List StD := []
theorem p15_I5 : LevelN true p15_T 5 p15_D5 := by intro s h; cases h
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
theorem p15_I7 : LevelN true p15_T 7 p15_D7 := levelStep p15_B p15_W p15_I6 (chunks 32 p15_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p15_C7x0
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p15_C10x0 : levelOK true p15_T p15_t 9 (p15_D9.map Prod.fst) ((p15_D10.drop (0*32)).take 32) = true := by decide +kernel
theorem p15_I10 : LevelN true p15_T 10 p15_D10 := levelStep p15_B p15_W p15_I9 (chunks 32 p15_D10 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p15_C10x0
  ))
theorem p15_L : LowN true p15_R p15_T 11 := lowSearch p15_B p15_I10 (by decide +kernel)
def p16_T : Nat := 0xfefefeeefefafca8fefefeeefefafca8fefefeeefefafca8fefefeeefefafca8
def p16_R : List Nat := [0, 1, 2, 3, 4, 5]
def p16_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,2,10),(4,1,17),(5,1,33)]
theorem p16_B : baseOK p16_T p16_R p16_E = true := by decide +kernel
def p16_Z : List SliceD := [(pw3,8,[0, 1, 2, 4, 5])]
theorem p16_Y : ∀ s ∈ p16_Z, SliceN true p16_R p16_T s := by
  unfold p16_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p16_B p3_B p3_L (by decide +kernel),by simp⟩
def p16_C : List (Nat × List Nat) := [(0,[])]
def p16_t : Tabs := (p16_C.map (mkCut true p16_Z),[],[],[[]])
theorem p16_W : TabsP true p16_R p16_T p16_t := ⟨cutsGood p16_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p16_D8 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw84],[0],[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])]
def p16_D7 : List StD := []
theorem p16_I7 : LevelN true p16_T 7 p16_D7 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p16_C8x0 : levelOK true p16_T p16_t 7 (p16_D7.map Prod.fst) ((p16_D8.drop (0*32)).take 32) = true := by decide +kernel
theorem p16_I8 : LevelN true p16_T 8 p16_D8 := levelStep p16_B p16_W p16_I7 (chunks 32 p16_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p16_C8x0
  ))
theorem p16_L : LowN true p16_R p16_T 9 := lowSearch p16_B p16_I8 (by decide +kernel)
def p17_T : Nat := 0xfffffffffffffefafffefffcffaacc00fffffffffffffefafffefffcffaacc00
def p17_R : List Nat := [0, 1, 2, 3, 4, 5, 6]
def p17_E : List (Nat × Nat × Nat) := [(0,16,17),(1,8,10),(2,32,36),(3,2,10),(4,1,17),(5,2,34),(6,1,65)]
theorem p17_B : baseOK p17_T p17_R p17_E = true := by decide +kernel
def p17_Z : List SliceD := [(pw85,9,[5, 3, 6, 4, 2, 1]),(pw137,7,[4, 3, 1, 5, 0]),(pw138,8,[6, 2, 4, 0, 5]),(pw86,8,[5, 2, 3, 1, 6]),(pw101,7,[3, 4, 0, 6, 1])]
theorem p17_Y : ∀ s ∈ p17_Z, SliceN true p17_R p17_T s := by
  unfold p17_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p17_B p16_B p16_L (by decide +kernel),mkSlice (w:=0) p17_B p9_B p9_L (by decide +kernel),mkSlice (w:=0) p17_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p17_B p3_B p3_L (by decide +kernel),mkSlice (w:=0) p17_B p9_B p9_L (by decide +kernel),by simp⟩
def p17_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(0,[257]),(2,[513]),(3,[513]),(0,[257,787]),(2,[513,647]),(3,[513,647]),(0,[257,538]),(2,[513,150]),(3,[513,150])]
def p17_t : Tabs := (p17_C.map (mkCut true p17_Z),[(19,18),(17,16),(21,20),(73,72),(49,48),(36,32),(14,12),(10,8),(24,16),(10,0),(50,48),(74,72),(14,6),(21,5),(17,1),(68,64),(36,4),(68,4),(40,32),(74,66),(49,33),(80,64),(96,64),(96,32),(70,66),(10,2),(10,6),(52,48),(37,33),(34,32),(76,72),(11,9),(11,3),(24,8),(19,3),(98,66),(68,0),(10,9),(10,3),(65,64),(17,3),(68,2),(17,9),(68,8),(68,16)],[],[[]])
theorem p17_W : TabsP true p17_R p17_T p17_t := ⟨cutsGood p17_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p17_D10 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw84,pw110],[4,8,0,1,21,25,33,12,16,13,53,41,49,61,65,5,9,17,29,37,45,57,69,73,77,81,85,89,93,3],[32780,65548,524,524,131084,524,262195,524386,2082,2082,1048611,4179,2098321,24849,4202769,4162,8388674,16777283,33555584,67110017,939540737])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p17_D9 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw84,pw110,pw114],[4,24,20,1,97,13,33,28,21,29,41,16,57,73,81,101,5,9,17,45,77,85,105,109,3],[65548,131084,44,44,262156,44,44,273,32834,1538,1538,524291,1538,4194307,8388625,273,273,16777233,32834,8258,1048579,8258,20608,2097281,20608,2049,1,2049])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p17_D8 : List StD := [
([pw123,pw0,pw1,pw4,pw10,pw84,pw110,pw114],[16,4,5,29,57,101,36,21,73,32,40,13,17,81,117,89,97,133,1,33,41,45,77,85,109,113,121,125,129,137,141],[33558660,82056,67109280,16785552,98307,129,1,134479884,268437540,133140,4613,2566,4612,16680,537919512,1073774601,2097226,16456,655408,353,4194402,352,9233,8389650,9232,3,2,1]),
([pw123,pw0,pw1,pw4,pw10,pw84,pw110],[48,4,44,52,17,29,81,117,5,57,73,101,145,93,149,153,157,161,165,169,173,177],[276,161,3073,584,2,12290,16389,32773,92,276,65542,161,131081,161,262147,524297,3073,1048579,584,2097162,4102])]
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
theorem p17_I9 : LevelN true p17_T 9 p17_D9 := levelStep p17_B p17_W p17_I8 (chunks 32 p17_D9 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p17_C9x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p17_C10x0 : levelOK true p17_T p17_t 9 (p17_D9.map Prod.fst) ((p17_D10.drop (0*32)).take 32) = true := by decide +kernel
theorem p17_I10 : LevelN true p17_T 10 p17_D10 := levelStep p17_B p17_W p17_I9 (chunks 32 p17_D10 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p17_C10x0
  ))
theorem p17_L : LowN true p17_R p17_T 11 := lowSearch p17_B p17_I10 (by decide +kernel)
def p18_T : Nat := 0xfeeefac8feeefac8feeefac8feeefac8feeefac8feeefac8feeefac8feeefac8
def p18_R : List Nat := [0, 1, 2, 3, 4]
def p18_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,1,9),(4,1,17)]
theorem p18_B : baseOK p18_T p18_R p18_E = true := by decide +kernel
def p18_Z : List SliceD := [(pw6,5,[0, 1, 4, 3])]
theorem p18_Y : ∀ s ∈ p18_Z, SliceN true p18_R p18_T s := by
  unfold p18_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p18_B p2_B p2_L (by decide +kernel),by simp⟩
def p18_C : List (Nat × List Nat) := [(0,[])]
def p18_t : Tabs := (p18_C.map (mkCut true p18_Z),[(9,8),(6,4),(3,2),(3,1),(6,2),(21,20)],[],[[]])
theorem p18_W : TabsP true p18_R p18_T p18_t := ⟨cutsGood p18_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p18_D5 : List StD := [
([pw0,pw1,pw2,pw4,pw10],[0,1,5,17,9,13,21],[54,75,17,3,33,5,5,9,9,1])]
def p18_D4 : List StD := []
theorem p18_I4 : LevelN true p18_T 4 p18_D4 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p18_C5x0 : levelOK true p18_T p18_t 4 (p18_D4.map Prod.fst) ((p18_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p18_I5 : LevelN true p18_T 5 p18_D5 := levelStep p18_B p18_W p18_I4 (chunks 32 p18_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p18_C5x0
  ))
theorem p18_L : LowN true p18_R p18_T 6 := lowSearch p18_B p18_I5 (by decide +kernel)
def p19_T : Nat := 0xfffefeeefff8fac8fffefeeefff8fac8fffefeeefff8fac8fffefeeefff8fac8
def p19_R : List Nat := [0, 1, 2, 3, 4, 5]
def p19_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,1,9),(4,4,20),(5,1,33)]
theorem p19_B : baseOK p19_T p19_R p19_E = true := by decide +kernel
def p19_Z : List SliceD := [(pw85,7,[1, 2, 3, 4, 5]),(pw5,7,[0, 3, 2, 4, 5]),(pw6,7,[3, 0, 1, 5, 4]),(pw3,7,[2, 1, 0, 5, 4]),(pw7,6,[0, 1, 2, 3, 5]),(pw10,6,[2, 3, 0, 1, 5])]
theorem p19_Y : ∀ s ∈ p19_Z, SliceN true p19_R p19_T s := by
  unfold p19_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p19_B p9_B p9_L (by decide +kernel),mkSlice (w:=0) p19_B p9_B p9_L (by decide +kernel),mkSlice (w:=0) p19_B p9_B p9_L (by decide +kernel),mkSlice (w:=0) p19_B p9_B p9_L (by decide +kernel),mkSlice (w:=0) p19_B p18_B p18_L (by decide +kernel),mkSlice (w:=16) p19_B p7_B p7_L (by decide +kernel),by simp⟩
def p19_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[])]
def p19_t : Tabs := (p19_C.map (mkCut true p19_Z),[(3,2),(9,8),(37,36),(19,18),(6,4),(3,1),(42,40),(19,17),(12,8),(6,2),(20,16),(44,40),(24,16),(9,1),(44,36),(20,4),(52,36)],[],[[]])
theorem p19_W : TabsP true p19_R p19_T p19_t := ⟨cutsGood p19_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p19_D8 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw84],[0,1,4,17,8,33,12,5,9,25,49,16,20,13,21,29,37,41,45,53,57,61,65],[131,259,131,8195,259,16396,524,32780,524,65584,131120,262192,525376,1049664,6297600])]
def p19_D7 : List StD := []
theorem p19_I7 : LevelN true p19_T 7 p19_D7 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p19_C8x0 : levelOK true p19_T p19_t 7 (p19_D7.map Prod.fst) ((p19_D8.drop (0*32)).take 32) = true := by decide +kernel
theorem p19_I8 : LevelN true p19_T 8 p19_D8 := levelStep p19_B p19_W p19_I7 (chunks 32 p19_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p19_C8x0
  ))
theorem p19_L : LowN true p19_R p19_T 9 := lowSearch p19_B p19_I8 (by decide +kernel)
def p20_T : Nat := 0xfffffffffffcffecfffffcecfff8f8a8fffffffffffcffecfffffcecfff8f8a8
def p20_R : List Nat := [0, 1, 2, 3, 4, 5, 6]
def p20_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,4,12),(4,4,20),(5,2,34),(6,2,66)]
theorem p20_B : baseOK p20_T p20_R p20_E = true := by decide +kernel
def p20_Z : List SliceD := [(pw85,9,[3, 4, 5, 6, 1, 2]),(pw3,9,[1, 5, 2, 4, 0, 6]),(pw7,9,[1, 6, 2, 3, 0, 5]),(pw83,9,[2, 3, 1, 6, 0, 4]),(pw103,9,[2, 4, 1, 5, 0, 3]),(pw139,5,[4, 3, 2, 5]),(pw140,6,[5, 6, 3, 4, 1]),(pw141,5,[6, 3, 4, 2])]
theorem p20_Y : ∀ s ∈ p20_Z, SliceN true p20_R p20_T s := by
  unfold p20_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p20_B p19_B p19_L (by decide +kernel),mkSlice (w:=0) p20_B p12_B p12_L (by decide +kernel),mkSlice (w:=0) p20_B p12_B p12_L (by decide +kernel),mkSlice (w:=0) p20_B p12_B p12_L (by decide +kernel),mkSlice (w:=0) p20_B p12_B p12_L (by decide +kernel),mkSlice (w:=0) p20_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p20_B p18_B p18_L (by decide +kernel),mkSlice (w:=2) p20_B p6_B p6_L (by decide +kernel),by simp⟩
def p20_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(0,[656]),(5,[]),(0,[659]),(1,[256]),(2,[256]),(3,[256]),(6,[]),(0,[657]),(7,[]),(1,[257]),(2,[257]),(0,[658]),(4,[257]),(1,[258]),(2,[258]),(3,[259]),(4,[259]),(1,[259]),(2,[259]),(3,[258]),(4,[258]),(1,[257,538]),(2,[257,538]),(4,[257,538])]
def p20_t : Tabs := (p20_C.map (mkCut true p20_Z),[(3,2),(5,4),(11,10),(19,18),(37,36),(69,68),(3,1),(5,1),(38,36),(14,10),(14,6),(12,4),(22,6),(20,4),(34,2),(48,16),(66,2),(72,8),(24,16),(24,8),(38,6),(70,6),(34,10),(66,18),(72,40),(7,6),(12,10),(66,0),(66,10),(34,18),(5,36),(70,68),(14,2),(22,2),(26,18),(26,10),(3,10),(3,18),(5,68),(7,1),(100,68),(100,36),(3,33),(3,0),(11,8),(19,16),(67,64)],[],[[]])
theorem p20_W : TabsP true p20_R p20_T p20_t := ⟨cutsGood p20_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p20_D10 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw84,pw110],[0,1,4,8,12,16,5,41,49,57,61,65,69,73,9,13,17,21,25,29,33,37,45,53,77,81,85,89,93,97,3],[67,67,16387,32771,65539,131075,1077673984,4194436,8388872,1552,6176,8324,16777480,33554960,67110944,8204,134217748,4132,1048,268435496,536870960])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p20_D9 : List StD := [
([pw0,pw142,pw1,pw2,pw4,pw10,pw84,pw110],[24,20,101,32,36,40,44,41,49,65,81,1,85,28,5,9,13,17,21,25,33,77,89,93,97,105,109,113,117],[2054,16390,2054,32774,65542,131078,262150,1048577,8193,137,273,1057,4609,33554497,137,273,1057,67633665,200,336,1120,4609,2097176,4194344,134217737,268435504,8388625,16777249]),
([pw0,pw1,pw2,pw19,pw4,pw10,pw84,pw110],[52,48,1,44,56,60,68,33,61,5,45,53,57,69,73,64,9,13,21,37,65,77,81,85,89,93,97,105,121,125,129,133,3],[518,518,4294967303,65542,131078,268435463,262150,134217865,9,1169,2209,4481,536871041,32769,1073742872,2147485736,4194569,9961544,16401,2097185,4353,8257,16432,16777233,8272,289,33554528,67108929]),
([pw87,pw0,pw1,pw2,pw4,pw10,pw84,pw110],[52,64,72,80,84,44,76,45,81,137,1,5,53,65,141,57,61,69,85,29,33,89,93,97,121,145,149,153,157],[3074,32,1,644,20544,33033,270352,3074,3074,33554438,67108930,16777226,134217746,270008353,645,20545,65801,139281,676,20576,33065,270384,644,2097165,131092,65609,4194384,8388889]),
([pw143,pw0,pw1,pw2,pw4,pw10,pw84,pw110],[44,28,88,92,96,100,52,161,1,5,45,53,165,48,29,37,77,89,93,113,117,121,145,149,153,157,169],[770,8193,16385,1029,2057,145,4129,770,770,4194310,8388618,2097170,16777250,33587265,1092,2120,67109072,4192,1029,2057,145,4129,65548,131092,524324,1048600,262184,176])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p20_D8 : List StD := [
([pw52,pw1,pw2,pw4,pw10,pw84,pw110],[52,173,5,104,112,108,57,48,33,45,73,9,13,21,53,65,77,81,85,89,93,97,113,117,121,177,181,185],[131,133,2053,4101,16777285,8197,259,33554435,67108867,323,134217731,1544,81952,131137,294928,1544,524297,4194328,8388641,1048624,2097169])]
def p20_D7 : List StD := []
theorem p20_I7 : LevelN true p20_T 7 p20_D7 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p20_C8x0 : levelOK true p20_T p20_t 7 (p20_D7.map Prod.fst) ((p20_D8.drop (0*32)).take 32) = true := by decide +kernel
theorem p20_I8 : LevelN true p20_T 8 p20_D8 := levelStep p20_B p20_W p20_I7 (chunks 32 p20_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p20_C8x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p20_C9x0 : levelOK true p20_T p20_t 8 (p20_D8.map Prod.fst) ((p20_D9.drop (0*32)).take 32) = true := by decide +kernel
theorem p20_I9 : LevelN true p20_T 9 p20_D9 := levelStep p20_B p20_W p20_I8 (chunks 32 p20_D9 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p20_C9x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p20_C10x0 : levelOK true p20_T p20_t 9 (p20_D9.map Prod.fst) ((p20_D10.drop (0*32)).take 32) = true := by decide +kernel
theorem p20_I10 : LevelN true p20_T 10 p20_D10 := levelStep p20_B p20_W p20_I9 (chunks 32 p20_D10 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p20_C10x0
  ))
theorem p20_L : LowN true p20_R p20_T 11 := lowSearch p20_B p20_I10 (by decide +kernel)
def p21_T : Nat := 0xfffffffffffffff0fffffcccfeaafc00fffffffffffffff0fffffcccfeaafc00
def p21_R : List Nat := [0, 1, 2, 3, 4, 5, 6]
def p21_E : List (Nat × Nat × Nat) := [(0,16,17),(1,8,10),(2,8,12),(3,2,10),(4,1,17),(5,2,34),(6,4,68)]
theorem p21_B : baseOK p21_T p21_R p21_E = true := by decide +kernel
def p21_Z : List SliceD := [(pw85,9,[6, 3, 5, 1, 4, 2])]
theorem p21_Y : ∀ s ∈ p21_Z, SliceN true p21_R p21_T s := by
  unfold p21_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p21_B p16_B p16_L (by decide +kernel),by simp⟩
def p21_C : List (Nat × List Nat) := [(0,[])]
def p21_t : Tabs := (p21_C.map (mkCut true p21_Z),[],[],[[]])
theorem p21_W : TabsP true p21_R p21_T p21_t := ⟨cutsGood p21_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p21_D9 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw84,pw110],[0],[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])]
def p21_D8 : List StD := []
theorem p21_I8 : LevelN true p21_T 8 p21_D8 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p21_C9x0 : levelOK true p21_T p21_t 8 (p21_D8.map Prod.fst) ((p21_D9.drop (0*32)).take 32) = true := by decide +kernel
theorem p21_I9 : LevelN true p21_T 9 p21_D9 := levelStep p21_B p21_W p21_I8 (chunks 32 p21_D9 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p21_C9x0
  ))
theorem p21_L : LowN true p21_R p21_T 10 := lowSearch p21_B p21_I9 (by decide +kernel)
def p22_T : Nat := 0xfffffffffffffcf0ffffffc0eeeaccc0fffffffffffffcf0ffffffc0eeeaccc0
def p22_R : List Nat := [0, 1, 2, 3, 4, 5, 6]
def p22_E : List (Nat × Nat × Nat) := [(0,16,17),(1,4,6),(2,2,6),(3,2,10),(4,1,17),(5,8,40),(6,4,68)]
theorem p22_B : baseOK p22_T p22_R p22_E = true := by decide +kernel
def p22_Z : List SliceD := [(pw85,9,[5, 6, 1, 2, 3, 4])]
theorem p22_Y : ∀ s ∈ p22_Z, SliceN true p22_R p22_T s := by
  unfold p22_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p22_B p12_B p12_L (by decide +kernel),by simp⟩
def p22_C : List (Nat × List Nat) := [(0,[])]
def p22_t : Tabs := (p22_C.map (mkCut true p22_Z),[],[],[[]])
theorem p22_W : TabsP true p22_R p22_T p22_t := ⟨cutsGood p22_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p22_D9 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw84,pw110],[0],[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])]
def p22_D8 : List StD := []
theorem p22_I8 : LevelN true p22_T 8 p22_D8 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p22_C9x0 : levelOK true p22_T p22_t 8 (p22_D8.map Prod.fst) ((p22_D9.drop (0*32)).take 32) = true := by decide +kernel
theorem p22_I9 : LevelN true p22_T 9 p22_D9 := levelStep p22_B p22_W p22_I8 (chunks 32 p22_D9 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p22_C9x0
  ))
theorem p22_L : LowN true p22_R p22_T 10 := lowSearch p22_B p22_I9 (by decide +kernel)
def p23_T : Nat := 0xfffffffefffefefefffffffefffefefefffffffefffefefefffffffefffefefe
def p23_R : List Nat := [0, 1, 2, 3, 4, 5]
def p23_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,0,4),(3,16,24),(4,8,24),(5,8,40)]
theorem p23_B : baseOK p23_T p23_R p23_E = true := by decide +kernel
def p23_Z : List SliceD := [(pw85,6,[1, 2, 3, 4, 5])]
theorem p23_Y : ∀ s ∈ p23_Z, SliceN true p23_R p23_T s := by
  unfold p23_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p23_B p7_B p7_L (by decide +kernel),by simp⟩
def p23_C : List (Nat × List Nat) := [(0,[])]
def p23_t : Tabs := (p23_C.map (mkCut true p23_Z),[(1,0),(2,0)],[],[[]])
theorem p23_W : TabsP true p23_R p23_T p23_t := ⟨cutsGood p23_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p23_D6 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw84],[0,1,5],[7,3,3,3,3,5,5,5,5,1,1,1,1,1,1])]
def p23_D5 : List StD := []
theorem p23_I5 : LevelN true p23_T 5 p23_D5 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p23_C6x0 : levelOK true p23_T p23_t 5 (p23_D5.map Prod.fst) ((p23_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p23_I6 : LevelN true p23_T 6 p23_D6 := levelStep p23_B p23_W p23_I5 (chunks 32 p23_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p23_C6x0
  ))
theorem p23_L : LowN true p23_R p23_T 7 := lowSearch p23_B p23_I6 (by decide +kernel)
def p24_T : Nat := 0xfffffffffffffffffffffffffffffec0fffffffffffffffffffffffffffffec0
def p24_R : List Nat := [0, 1, 2, 3, 4, 5, 6]
def p24_E : List (Nat × Nat × Nat) := [(0,8,9),(1,4,6),(2,2,6),(3,1,9),(4,0,16),(5,0,32),(6,0,64)]
theorem p24_B : baseOK p24_T p24_R p24_E = true := by decide +kernel
def p24_Z : List SliceD := [(pw85,7,[4, 5, 6, 1, 2, 3])]
theorem p24_Y : ∀ s ∈ p24_Z, SliceN true p24_R p24_T s := by
  unfold p24_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p24_B p23_B p23_L (by decide +kernel),by simp⟩
def p24_C : List (Nat × List Nat) := [(0,[])]
def p24_t : Tabs := (p24_C.map (mkCut true p24_Z),[(9,8),(6,4)],[],[[]])
theorem p24_W : TabsP true p24_R p24_T p24_t := ⟨cutsGood p24_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p24_D7 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw84,pw110],[0,1,5],[7,3,1,3,3,3,1,5,5,5,5,1,1,1,1,1,1,1,1,1,1])]
def p24_D6 : List StD := []
theorem p24_I6 : LevelN true p24_T 6 p24_D6 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p24_C7x0 : levelOK true p24_T p24_t 6 (p24_D6.map Prod.fst) ((p24_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p24_I7 : LevelN true p24_T 7 p24_D7 := levelStep p24_B p24_W p24_I6 (chunks 32 p24_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p24_C7x0
  ))
theorem p24_L : LowN true p24_R p24_T 8 := lowSearch p24_B p24_I7 (by decide +kernel)
def p25_T : Nat := 0xfeeefaeafcecf8e8feeefaeafcecf8e8feeefaeafcecf8e8feeefaeafcecf8e8
def p25_R : List Nat := [0, 1, 2, 3, 4, 5]
def p25_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,4,12),(4,2,18),(5,1,33)]
theorem p25_B : baseOK p25_T p25_R p25_E = true := by decide +kernel
def p25_Z : List SliceD := [(pw8,4,[0, 2, 3, 5]),(pw144,4,[1, 2, 3, 4]),(pw9,4,[0, 1, 4, 5]),(pw3,6,[0, 1, 2, 4, 5]),(pw7,6,[0, 2, 1, 3, 5]),(pw83,6,[1, 2, 0, 3, 4]),(pw145,4,[0, 2, 3, 5]),(pw146,4,[1, 2, 3, 4]),(pw4,5,[2, 1, 0, 5, 4]),(pw147,4,[0, 1, 4, 5])]
theorem p25_Y : ∀ s ∈ p25_Z, SliceN true p25_R p25_T s := by
  unfold p25_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p25_B p8_B p8_L (by decide +kernel),mkSlice (w:=0) p25_B p8_B p8_L (by decide +kernel),mkSlice (w:=0) p25_B p8_B p8_L (by decide +kernel),mkSlice (w:=0) p25_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p25_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p25_B p5_B p5_L (by decide +kernel),mkSlice (w:=16) p25_B p8_B p8_L (by decide +kernel),mkSlice (w:=32) p25_B p8_B p8_L (by decide +kernel),mkSlice (w:=8) p25_B p13_B p13_L (by decide +kernel),mkSlice (w:=8) p25_B p8_B p8_L (by decide +kernel),by simp⟩
def p25_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(9,[]),(4,[385]),(5,[393]),(3,[385]),(5,[521]),(3,[512]),(3,[514]),(4,[514]),(4,[393]),(5,[385]),(3,[390]),(5,[514]),(3,[517]),(4,[521]),(4,[390]),(5,[390]),(3,[393]),(5,[517]),(3,[521]),(4,[517])]
def p25_t : Tabs := (p25_C.map (mkCut true p25_Z),[(6,4),(3,2),(3,1),(5,4),(5,1),(3,10),(11,2),(5,20),(18,2),(33,1),(33,0),(6,2),(3,9),(11,1),(18,0),(6,36),(12,4),(12,0),(5,17),(6,34),(18,10),(33,9),(33,17),(18,17),(35,2),(3,17),(19,1),(12,8),(12,9),(37,4),(18,16),(5,9),(13,1),(33,40),(49,56),(33,48),(41,56),(11,9),(41,9),(49,17),(41,8),(49,16),(33,32),(12,10),(22,4),(6,10),(14,2),(18,24),(21,20),(18,56),(26,10),(50,34),(11,10),(18,8),(18,32),(18,48),(26,56),(28,20),(44,36),(12,16),(12,32),(12,24),(12,56),(12,40),(12,20),(44,4),(33,56),(26,2),(50,2),(28,4),(33,16),(41,1),(33,8),(49,1),(12,36),(18,34)],[],[[]])
theorem p25_W : TabsP true p25_R p25_T p25_t := ⟨cutsGood p25_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p25_D7 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw84],[3,0,4,8,12,16,20,1,5,17,33,37,9,13,21,25,29,41,45,49,53,57,61,65,69,73,77,81,85,89],[4487,8973,49429,66855,133445,266379,1573011,2098339,4196547,25166361,33556011,67111501,134217786,268435548,536871014])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p25_D6 : List StD := [
([pw0,pw1,pw11,pw2,pw4,pw10,pw84],[24,17,5,9,28,37,65,45,109,12,16,20,32,1,13,21,25,49,93,97,101,105],[262156,16384,134,98308,5,524324,8192,138,131081,3145736,24,258,4672,1025,2096,258,3,18,65,112,33]),
([pw0,pw1,pw2,pw13,pw4,pw10,pw84],[36,9,13,33,17,37,28,1,121,12,16,20,24,5,29,45,61,73,113,117,125,129],[134,262164,8192,5,16396,524324,130,258,3,266,65570,32768,3145744,131089,80,513,5128,2144,9,33,72]),
([pw0,pw1,pw2,pw15,pw10,pw84],[36,28,45,40,1,33,133,9,17,65,21,3,12,44,37,57,73,137],[1232,325,4097,131170,1090,389,2705,34872,24594,261,65549,7,553,515,42]),
([pw0,pw1,pw2,pw4,pw17,pw84],[24,28,1,29,45,65,48,9,33,141,3,52,5,17,37,69,145,149],[141,8728,65578,4099,522,133,131077,133,7,33904,1297,18450,97,98,259]),
([pw148,pw0,pw1,pw2,pw4,pw10],[28,3,1,17,97,60,64,37,65,56,9,33,20,41,45,57,69,73,81,117,149,153,157,161,165],[4608,1159,139,2097665,4194433,8209,524305,8388625,16777233,17420,1048870,34886,65834,133194,262496]),
([pw0,pw1,pw2,pw19,pw4,pw10,pw84],[13,33,36,1,37,45,24,5,169,12,16,20,28,9,17,21,25,29,61,77,173,177,181,185],[129,129,257,98305,131075,257,1048616,8192,12,2097162,262168,16384,12582944,98,524324,516,1090,6160,6,20,82]),
([pw0,pw1,pw2,pw20,pw10,pw84],[36,24,13,45,72,189,5,17,65,68,33,37,49,3,9,41,77,193,197],[4196,204,8517,132614,43028,169,16387,4130,262194,137,11,65561,259,2321,1538]),
([pw149,pw0,pw1,pw2,pw4,pw84],[24,3,13,76,80,33,45,65,5,37,105,9,17,41,57,69,77,85,177,201,205,209,213,217],[295,2049,99,524321,1048609,17413,4420,2097294,8726,263169,4194313,8388625,32970,66130,131224]),
([pw0,pw1,pw2,pw4,pw10,pw150],[28,24,13,17,61,65,84,5,88,221,3,9,33,37,45,69,193,209,225],[149,133,131077,65541,133,16920,262194,530,2051,33896,4362,9225,98,97,259]),
([pw151,pw0,pw1,pw2,pw10,pw84],[36,3,5,92,96,1,65,33,13,37,129,9,17,41,57,61,69,89,185,193,229,233,237,241],[327,99,4097,1048641,2097217,2340,66565,524430,8726,263169,16554,33330,4194313,8388625,131224]),
([pw0,pw1,pw2,pw4,pw21,pw84],[36,24,1,13,100,104,65,245,5,9,33,37,73,3,17,41,61,209,249],[780,4488,131161,9482,43048,646,85,518,65574,4225,16387,262305,81,81,3106]),
([pw0,pw1,pw2,pw4,pw10,pw152],[28,36,1,13,77,108,112,5,9,33,65,253,3,17,37,57,149,193,209,249],[396,153,262153,131081,137,2324,66598,37444,20741,2066,524370,8195,1058,35,577])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p25_D5 : List StD := [
([pw39,pw0,pw1,pw2,pw10,pw84],[5,33,45,37,17,133,1,65,9,57,61,73,77,89,257,261,265],[33,256,20,16514,32904,33,21,65539,33,20,578,1096,2054,4108,8202]),
([pw149,pw0,pw1,pw2,pw15,pw84],[45,17,21,33,37,65,133,57,5,9,77,213,217,261,269,273],[76,512,11,16424,32792,68,7,256,68,3,2208,4240,3,1041,8240]),
([pw151,pw0,pw1,pw2,pw17,pw84],[1,9,29,37,65,33,141,129,5,17,61,69,241,261,273,277],[84,19,512,32816,8216,7,68,256,68,3,3,1033,2208,4232,16424]),
([pw47,pw0,pw1,pw2,pw4,pw84],[1,13,65,37,9,141,33,45,17,49,61,69,77,81,85,265,273],[34,17,256,8260,65608,19,34,32774,34,17,517,1033,2180,4232,16396]),
([pw0,pw1,pw153,pw2,pw4,pw10],[5,17,33,9,37,45,65,109,1,21,25,41,49,53,73,81,89,93,105,281,285],[131081,2049,35,1537,524293,256,42,12296,262156,130,1048656,65556,130,16390,32836]),
([pw0,pw1,pw2,pw154,pw4,pw10],[9,13,33,65,17,1,37,121,29,41,45,49,73,81,85,113,129,289,293],[35,32786,514,131082,262,33,129,2057,133,1024,65560,4116,16456,262212,8204]),
([pw148,pw0,pw1,pw2,pw20,pw10],[45,17,33,189,49,65,37,41,5,9,73,277,281,285,289,293],[256,24,3,8288,32836,24,3,16544,4228,11,512,24,3,1029,2084]),
([pw148,pw149,pw0,pw1,pw2,pw4],[17,65,33,37,45,105,57,97,5,9,41,69,213,269,285,289,3],[65548,256,104,25,16394,1156,512,21,8198,96,17,32898,49,4130,2051]),
([pw148,pw151,pw0,pw1,pw2,pw10],[9,33,1,37,65,129,69,117,5,17,41,57,237,277,281,293,3],[65560,256,13,104,32778,1168,21,512,8210,5,96,16514,5,2051,4130]),
([pw148,pw0,pw1,pw2,pw4,pw21],[1,9,65,33,73,245,37,41,5,17,49,269,281,285,289,293],[256,3,48,8260,32840,3,48,16516,4232,3,1029,3,48,512,2060]),
([pw54,pw0,pw1,pw2,pw10,pw84],[9,17,37,33,45,189,13,65,5,29,41,73,77,89,197,277,297],[256,33,18,32904,65668,33,18,584,1092,19,33,16389,2058,4102,8204]),
([pw0,pw155,pw1,pw2,pw4,pw84],[17,37,57,5,65,9,33,45,109,13,21,25,49,77,85,97,217,269,301],[512,36,137,3080,32778,36,257,131152,262210,133,4116,65542,257,8195,16402]),
([pw0,pw1,pw2,pw156,pw4,pw84],[13,1,33,37,65,45,5,169,17,21,25,57,77,81,85,173,185,213,217,273],[65,65,133,1537,129,32802,2054,131090,262154,256,65584,4136,8212,524300,16408]),
([pw149,pw151,pw0,pw1,pw2,pw84],[5,37,13,33,65,185,69,177,9,17,41,57,217,241,261,273,3],[65560,13,256,104,32778,21,2192,512,16402,5,5,1027,96,4226,8226]),
([pw149,pw0,pw1,pw2,pw4,pw152],[13,5,65,33,37,77,253,57,9,17,21,177,213,269,273,285],[3,256,104,8204,16408,3,3,1029,3,96,4228,2192,96,512,32788]),
([pw151,pw0,pw1,pw2,pw10,pw150],[5,13,33,37,61,65,221,69,9,17,29,185,237,261,277,293],[3,112,512,16420,8232,3,3,1029,3,80,80,256,4228,2184,32780]),
([pw157,pw0,pw1,pw2,pw4,pw10],[13,65,1,33,5,221,17,37,21,29,45,69,73,81,85,197,293],[17,36,1024,16514,65672,17,17,259,521,36,32774,36,2114,4168,8202]),
([pw0,pw158,pw1,pw2,pw10,pw84],[9,33,37,13,69,65,1,17,121,5,29,61,89,117,237,241,277,297],[512,73,152,1034,8204,289,144,65570,131108,65,259,2053,16402,32788,4102]),
([pw0,pw1,pw159,pw2,pw10,pw84],[13,33,37,65,69,1,5,45,169,9,29,61,89,177,237,241,257,261],[65,265,65,1027,257,512,144,8226,2084,152,65546,131084,16402,32788,4102]),
([pw56,pw0,pw1,pw2,pw4,pw84],[9,37,17,65,1,245,5,33,13,21,41,49,61,85,249,269,301],[256,17,36,32904,65666,17,36,584,1090,17,2057,4099,36,16390,8202]),
([pw160,pw0,pw1,pw2,pw4,pw10],[5,33,45,65,13,253,9,37,1,21,29,49,57,81,89,249,285],[17,256,36,65672,16514,17,17,521,1027,36,2120,4162,36,32774,8202])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p25_D4 : List StD := [
([pw161,pw0,pw1,pw2,pw4],[5,17,33,57,65,109,9,13,21,45,49,269],[133,76,38,2068,73,35,273,522,1048,34]),
([pw162,pw0,pw1,pw2,pw10],[9,13,65,33,69,121,17,1,5,29,237,277],[262,37,84,2060,35,82,522,129,33,1048]),
([pw163,pw0,pw1,pw2,pw84],[5,65,1,37,69,169,9,13,17,45,217,241,261],[35,70,274,4106,33,129,33,532,1036,2072])]
def p25_D3 : List StD := []
theorem p25_I3 : LevelN true p25_T 3 p25_D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p25_C4x0 : levelOK true p25_T p25_t 3 (p25_D3.map Prod.fst) ((p25_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p25_I4 : LevelN true p25_T 4 p25_D4 := levelStep p25_B p25_W p25_I3 (chunks 32 p25_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p25_C4x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p25_C5x0 : levelOK true p25_T p25_t 4 (p25_D4.map Prod.fst) ((p25_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p25_I5 : LevelN true p25_T 5 p25_D5 := levelStep p25_B p25_W p25_I4 (chunks 32 p25_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p25_C5x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p25_C6x0 : levelOK true p25_T p25_t 5 (p25_D5.map Prod.fst) ((p25_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p25_I6 : LevelN true p25_T 6 p25_D6 := levelStep p25_B p25_W p25_I5 (chunks 32 p25_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p25_C6x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p25_C7x0 : levelOK true p25_T p25_t 6 (p25_D6.map Prod.fst) ((p25_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p25_I7 : LevelN true p25_T 7 p25_D7 := levelStep p25_B p25_W p25_I6 (chunks 32 p25_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p25_C7x0
  ))
theorem p25_L : LowN true p25_R p25_T 8 := lowSearch p25_B p25_I7 (by decide +kernel)
def p26_T : Nat := 0xfeeefeeafeeefeeafeeefeeafeeefeeafeeefeeafeeefeeafeeefeeafeeefeea
def p26_R : List Nat := [0, 1, 2, 3, 4]
def p26_E : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6),(3,2,10),(4,2,18)]
theorem p26_B : baseOK p26_T p26_R p26_E = true := by decide +kernel
def p26_Z : List SliceD := [(pw85,5,[1, 2, 3, 4])]
theorem p26_Y : ∀ s ∈ p26_Z, SliceN true p26_R p26_T s := by
  unfold p26_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p26_B p2_B p2_L (by decide +kernel),by simp⟩
def p26_C : List (Nat × List Nat) := [(0,[])]
def p26_t : Tabs := (p26_C.map (mkCut true p26_Z),[(1,0),(6,4),(3,2)],[],[[]])
theorem p26_W : TabsP true p26_R p26_T p26_t := ⟨cutsGood p26_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p26_D5 : List StD := [
([pw0,pw1,pw2,pw4,pw10],[0,1,5,9],[15,3,3,3,1,5,5,1,1,1])]
def p26_D4 : List StD := []
theorem p26_I4 : LevelN true p26_T 4 p26_D4 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p26_C5x0 : levelOK true p26_T p26_t 4 (p26_D4.map Prod.fst) ((p26_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p26_I5 : LevelN true p26_T 5 p26_D5 := levelStep p26_B p26_W p26_I4 (chunks 32 p26_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p26_C5x0
  ))
theorem p26_L : LowN true p26_R p26_T 6 := lowSearch p26_B p26_I5 (by decide +kernel)
def p27_T : Nat := 0xfffefefefffefeeefffefefefffefeeefffefefefffefeeefffefefefffefeee
def p27_R : List Nat := [0, 1, 2, 3, 4, 5]
def p27_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,8,12),(3,4,12),(4,4,20),(5,4,36)]
theorem p27_B : baseOK p27_T p27_R p27_E = true := by decide +kernel
def p27_Z : List SliceD := [(pw85,6,[1, 2, 3, 4, 5])]
theorem p27_Y : ∀ s ∈ p27_Z, SliceN true p27_R p27_T s := by
  unfold p27_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p27_B p26_B p26_L (by decide +kernel),by simp⟩
def p27_C : List (Nat × List Nat) := [(0,[])]
def p27_t : Tabs := (p27_C.map (mkCut true p27_Z),[(1,0),(2,0)],[],[[]])
theorem p27_W : TabsP true p27_R p27_T p27_t := ⟨cutsGood p27_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p27_D6 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw84],[0,1,5],[7,3,3,3,3,5,5,5,5,1,1,1,1,1,1])]
def p27_D5 : List StD := []
theorem p27_I5 : LevelN true p27_T 5 p27_D5 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p27_C6x0 : levelOK true p27_T p27_t 5 (p27_D5.map Prod.fst) ((p27_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p27_I6 : LevelN true p27_T 6 p27_D6 := levelStep p27_B p27_W p27_I5 (chunks 32 p27_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p27_C6x0
  ))
theorem p27_L : LowN true p27_R p27_T 7 := lowSearch p27_B p27_I6 (by decide +kernel)
def p28_T : Nat := 0xfffefefeffeefaaafffefefeffeefaaafffefefeffeefaaafffefefeffeefaaa
def p28_R : List Nat := [0, 1, 2, 3, 4, 5]
def p28_E : List (Nat × Nat × Nat) := [(0,0,1),(1,16,18),(2,8,12),(3,4,12),(4,2,18),(5,2,34)]
theorem p28_B : baseOK p28_T p28_R p28_E = true := by decide +kernel
def p28_Z : List SliceD := [(pw85,7,[1, 2, 3, 4, 5])]
theorem p28_Y : ∀ s ∈ p28_Z, SliceN true p28_R p28_T s := by
  unfold p28_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p28_B p10_B p10_L (by decide +kernel),by simp⟩
def p28_C : List (Nat × List Nat) := [(0,[])]
def p28_t : Tabs := (p28_C.map (mkCut true p28_Z),[],[],[[]])
theorem p28_W : TabsP true p28_R p28_T p28_t := ⟨cutsGood p28_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p28_D7 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw84],[0],[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])]
def p28_D6 : List StD := []
theorem p28_I6 : LevelN true p28_T 6 p28_D6 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p28_C7x0 : levelOK true p28_T p28_t 6 (p28_D6.map Prod.fst) ((p28_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p28_I7 : LevelN true p28_T 7 p28_D7 := levelStep p28_B p28_W p28_I6 (chunks 32 p28_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p28_C7x0
  ))
theorem p28_L : LowN true p28_R p28_T 8 := lowSearch p28_B p28_I7 (by decide +kernel)
def p29_T : Nat := 0xfffffffffffffffffffffffffeeefac0fffffffffffffffffffffffffeeefac0
def p29_R : List Nat := [0, 1, 2, 3, 4, 5, 6]
def p29_E : List (Nat × Nat × Nat) := [(0,8,9),(1,4,6),(2,2,6),(3,1,9),(4,1,17),(5,0,32),(6,0,64)]
theorem p29_B : baseOK p29_T p29_R p29_E = true := by decide +kernel
def p29_Z : List SliceD := [(pw83,8,[6, 1, 3, 0, 4, 2])]
theorem p29_Y : ∀ s ∈ p29_Z, SliceN true p29_R p29_T s := by
  unfold p29_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p29_B p28_B p28_L (by decide +kernel),by simp⟩
def p29_C : List (Nat × List Nat) := [(0,[])]
def p29_t : Tabs := (p29_C.map (mkCut true p29_Z),[],[],[[]])
theorem p29_W : TabsP true p29_R p29_T p29_t := ⟨cutsGood p29_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p29_D8 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw84,pw110],[0],[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])]
def p29_D7 : List StD := []
theorem p29_I7 : LevelN true p29_T 7 p29_D7 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p29_C8x0 : levelOK true p29_T p29_t 7 (p29_D7.map Prod.fst) ((p29_D8.drop (0*32)).take 32) = true := by decide +kernel
theorem p29_I8 : LevelN true p29_T 8 p29_D8 := levelStep p29_B p29_W p29_I7 (chunks 32 p29_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p29_C8x0
  ))
theorem p29_L : LowN true p29_R p29_T 9 := lowSearch p29_B p29_I8 (by decide +kernel)
def p30_T : Nat := 0xfffffffffffffffffffffffffffafc88fffffffffffffffffffffffffffafc88
def p30_R : List Nat := [0, 1, 2, 3, 4, 5, 6]
def p30_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,8,12),(3,2,10),(4,1,17),(5,0,32),(6,0,64)]
theorem p30_B : baseOK p30_T p30_R p30_E = true := by decide +kernel
def p30_Z : List SliceD := [(pw85,7,[5, 6, 3, 4, 2, 1])]
theorem p30_Y : ∀ s ∈ p30_Z, SliceN true p30_R p30_T s := by
  unfold p30_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p30_B p27_B p27_L (by decide +kernel),by simp⟩
def p30_C : List (Nat × List Nat) := [(0,[])]
def p30_t : Tabs := (p30_C.map (mkCut true p30_Z),[(17,16),(10,8),(3,2),(3,1),(12,8),(7,6),(13,9),(10,2)],[],[[]])
theorem p30_W : TabsP true p30_R p30_T p30_t := ⟨cutsGood p30_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p30_D7 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw84,pw110],[0,1,5,17,29,9,13,21,25],[102,394,19,33,3,3,13,65,5,5,5,1,9,9,9,17,17,17,1,1,1])]
def p30_D6 : List StD := []
theorem p30_I6 : LevelN true p30_T 6 p30_D6 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p30_C7x0 : levelOK true p30_T p30_t 6 (p30_D6.map Prod.fst) ((p30_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p30_I7 : LevelN true p30_T 7 p30_D7 := levelStep p30_B p30_W p30_I6 (chunks 32 p30_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p30_C7x0
  ))
theorem p30_L : LowN true p30_R p30_T 8 := lowSearch p30_B p30_I7 (by decide +kernel)
def ptopT : Nat := 0xfffffffffffffffeffffffffffeeffeefffffefefffffafafefefefceeeeaa00
def ptopR : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]
def ptopE : List (Nat × Nat × Nat) := [(0,8,9),(1,16,18),(2,32,36),(3,1,9),(4,1,17),(5,2,34),(6,1,65),(7,1,129)]
theorem ptopB : baseOK ptopT ptopR ptopE = true := by decide +kernel
def ptopZ : List SliceD := [(pw5,11,[2, 5, 4, 3, 7, 6, 0]),(pw6,11,[5, 6, 3, 4, 1, 0, 7]),(pw3,11,[2, 5, 6, 0, 4, 1, 7]),(pw7,11,[2, 6, 1, 3, 0, 5, 7]),(pw83,10,[2, 1, 3, 7, 6, 4, 0]),(pw85,10,[3, 6, 2, 4, 7, 1, 5]),(pw103,10,[2, 4, 3, 0, 5, 1, 7]),(pw164,10,[3, 5, 1, 2, 0, 6, 4]),(pw84,8,[3, 4, 6, 0, 1, 2, 7]),(pw144,7,[6, 7, 1, 4, 3, 2]),(pw165,8,[1, 5, 7, 3, 2, 4]),(pw166,7,[1, 2, 6, 4, 5]),(pw167,7,[2, 4, 7, 1, 5, 3]),(pw168,7,[1, 2, 0, 4, 6, 3]),(pw169,8,[0, 4, 6, 2, 1, 3]),(pw170,7,[0, 5, 1, 4, 2, 3]),(pw4,9,[1, 2, 6, 4, 5, 0, 7]),(pw105,6,[0, 7, 1, 4, 3]),(pw171,7,[1, 7, 0, 4, 6, 3]),(pw2,8,[1, 4, 3, 0, 7, 5, 6]),(pw172,9,[1, 5, 6, 2, 4, 7]),(pw173,9,[7, 0, 4, 6, 3, 5]),(pw174,9,[6, 0, 3, 7, 4, 2]),(pw175,7,[1, 2, 6, 4, 5]),(pw176,9,[5, 7, 3, 0, 1, 2])]
theorem ptopY : ∀ s ∈ ptopZ, SliceN true ptopR ptopT s := by
  unfold ptopZ
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) ptopB p15_B p15_L (by decide +kernel),mkSlice (w:=0) ptopB p17_B p17_L (by decide +kernel),mkSlice (w:=0) ptopB p20_B p20_L (by decide +kernel),mkSlice (w:=0) ptopB p15_B p15_L (by decide +kernel),mkSlice (w:=0) ptopB p21_B p21_L (by decide +kernel),mkSlice (w:=0) ptopB p22_B p22_L (by decide +kernel),mkSlice (w:=0) ptopB p21_B p21_L (by decide +kernel),mkSlice (w:=0) ptopB p22_B p22_L (by decide +kernel),mkSlice (w:=32) ptopB p24_B p24_L (by decide +kernel),mkSlice (w:=0) ptopB p14_B p14_L (by decide +kernel),mkSlice (w:=0) ptopB p25_B p25_L (by decide +kernel),mkSlice (w:=0) ptopB p10_B p10_L (by decide +kernel),mkSlice (w:=64) ptopB p27_B p27_L (by decide +kernel),mkSlice (w:=32) ptopB p27_B p27_L (by decide +kernel),mkSlice (w:=0) ptopB p25_B p25_L (by decide +kernel),mkSlice (w:=0) ptopB p14_B p14_L (by decide +kernel),mkSlice (w:=8) ptopB p29_B p29_L (by decide +kernel),mkSlice (w:=0) ptopB p18_B p18_L (by decide +kernel),mkSlice (w:=32) ptopB p27_B p27_L (by decide +kernel),mkSlice (w:=4) ptopB p30_B p30_L (by decide +kernel),mkSlice (w:=0) ptopB p12_B p12_L (by decide +kernel),mkSlice (w:=0) ptopB p4_B p4_L (by decide +kernel),mkSlice (w:=0) ptopB p4_B p4_L (by decide +kernel),mkSlice (w:=8) ptopB p10_B p10_L (by decide +kernel),mkSlice (w:=0) ptopB p4_B p4_L (by decide +kernel),by simp⟩
def ptopC : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(0,[773]),(1,[641]),(3,[657]),(2,[389]),(6,[525]),(8,[]),(9,[]),(7,[517]),(1,[645]),(3,[517]),(2,[393]),(4,[785]),(0,[789]),(10,[]),(7,[657]),(0,[785]),(1,[789]),(2,[781]),(3,[785]),(4,[781]),(11,[]),(6,[781]),(0,[645]),(1,[129]),(2,[261]),(5,[773]),(3,[645]),(12,[]),(7,[645]),(13,[]),(0,[517]),(1,[769]),(5,[785]),(2,[773]),(3,[789]),(6,[785]),(14,[]),(0,[657]),(1,[773]),(5,[517]),(2,[777]),(3,[773]),(4,[525]),(15,[]),(1,[641,789]),(0,[773,785]),(3,[657,785]),(2,[389,781]),(0,[773,645]),(1,[641,129]),(2,[389,261]),(3,[657,645]),(0,[773,517]),(1,[641,769]),(2,[389,773]),(6,[525,785]),(3,[657,789]),(1,[129,669]),(2,[261,413]),(3,[517,669]),(0,[645,797]),(5,[775]),(0,[773,670]),(1,[641,158]),(2,[389,286]),(3,[657,158]),(0,[517,797]),(1,[641,797]),(2,[389,797]),(3,[657,797]),(6,[525,797]),(16,[]),(1,[790]),(1,[642,798]),(0,[773,542]),(1,[641,798]),(2,[389,798]),(3,[657,798]),(6,[525,798]),(5,[787]),(0,[773,657]),(1,[641,773]),(2,[389,777]),(3,[657,773]),(1,[645,769]),(3,[517,789]),(0,[789,517]),(2,[393,773]),(10,[261]),(0,[789,657]),(1,[645,773]),(2,[393,777]),(3,[517,773]),(4,[785,525]),(1,[645,797]),(2,[393,797]),(3,[517,797]),(4,[525,797]),(0,[657,797]),(7,[515]),(0,[785,414]),(1,[789,286]),(3,[785,414]),(4,[781,286]),(5,[515]),(6,[781,286]),(0,[645,785]),(2,[261,781]),(1,[129,789]),(11,[521]),(3,[785,645]),(17,[]),(0,[785,657]),(2,[781,777]),(1,[789,773]),(3,[785,773]),(0,[645,798]),(1,[129,670]),(2,[261,414]),(3,[645,542]),(1,[642]),(1,[131,670]),(0,[645,899]),(2,[261,899]),(3,[645,899]),(6,[515]),(7,[645,911]),(18,[]),(19,[]),(0,[645,30]),(2,[261,30]),(3,[645,30]),(4,[515]),(7,[645,414]),(1,[129,773]),(2,[261,777]),(3,[645,773]),(0,[657,645]),(1,[129,774]),(1,[129,797]),(0,[517,669]),(3,[645,797]),(2,[261,797]),(0,[645,542]),(2,[261,798]),(3,[645,798]),(0,[657,798]),(1,[773,670]),(2,[777,414]),(3,[773,542]),(1,[646,798]),(7,[659]),(0,[657,158]),(1,[773,30]),(2,[777,158]),(3,[773,670]),(1,[128]),(0,[785,657,773]),(1,[641,773,789]),(2,[389,781,777]),(3,[657,785,773]),(11,[521,150]),(20,[261,410]),(21,[389,665]),(22,[129,666]),(22,[131,409]),(11,[523]),(23,[523]),(24,[129,409]),(12,[650]),(0,[645,785,418]),(1,[129,789,290]),(13,[650]),(3,[645,785,418]),(0,[785,645,34]),(3,[785,645,34]),(22,[385,666]),(24,[129,666]),(22,[]),(22,[129,409]),(11,[522]),(23,[522]),(24,[131,409])]
def ptopt : Tabs := (ptopC.map (mkCut true ptopZ),[(35,33),(18,16),(37,33),(36,32),(9,1),(136,128),(17,1),(18,2),(34,2),(41,40),(35,3),(65,64),(65,1),(129,128),(129,1),(18,20),(9,3),(98,96),(130,128),(9,5),(17,5),(36,0),(68,64),(196,192),(18,10),(41,33),(200,192),(49,33),(80,64),(208,192),(98,66),(97,33),(160,128),(160,32),(196,132),(194,66),(34,33),(36,33),(49,48),(97,96),(26,24),(34,32),(44,40),(52,48),(26,10),(9,33),(17,33),(65,33),(129,33),(68,4),(130,2),(67,66),(73,72),(193,192),(70,66),(11,3),(36,4),(65,3),(129,3),(129,5),(161,33),(9,8),(17,0),(34,96),(112,56),(224,192),(160,96),(17,16),(9,0),(160,48),(224,96),(68,192),(136,192),(80,192),(41,32),(112,48),(37,1),(136,24),(152,144),(176,144),(36,132),(37,5),(67,3),(130,6),(129,192),(133,132),(145,144),(73,64),(136,16),(200,64),(22,20),(13,5),(21,5),(65,192),(130,3),(9,10),(130,10),(68,0),(11,8),(69,1),(17,3),(68,2),(36,8),(68,8),(36,16),(68,16),(164,128),(196,128),(11,10),(13,12),(160,192),(106,74),(120,56),(168,40),(129,0),(9,12),(208,144),(13,8),(15,10),(21,16),(133,128),(52,16),(84,16),(152,24),(36,128),(70,6),(131,3),(80,16),(133,5),(76,12),(176,48),(11,2),(13,4),(25,16),(11,1),(44,8),(133,1),(140,8),(69,5),(130,66),(136,0),(70,2),(152,16)],[],[[]])
theorem ptopW : TabsP true ptopR ptopT ptopt := ⟨cutsGood ptopY (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD12 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw84,pw110,pw177],[0,4,8,12,3,1,16,9,17,25,20,24,28,5,33,37,21,49,13,29,41,45,53,57,61,65,69,73,77,81,85,89,93,97,101,105,109,113,117,121,125,129,133,137,141],[8225,262274,65796,524808,1098832,2264080,12620816,16777219,33554437,8225,8225,67108897,134217761,268435462,536870922,1073742018,2147483778,4294967426,8589934604,17179869444,34359738628,65796,68719477256,137438953992,274877907464,1649267460176,6597069787216,26388279203856])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD11 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw84,pw178,pw110,pw177],[20,16,32,36,169,3,40,161,44,37,177,17,165,48,52,56,21,25,41,57,89,153,197,28,60,5,13,49,61,69,73,93,105,113,117,137,141,145,149,157,173,181,185,189,193,201],[137438953477,274877906953,2097665,2097665,3,3,549755814401,524833,268435468,33554564,4228,4102,4228,536871044,1073741956,67108888,1099511627800,26,1048600,1048600,2147483672,132160,2199023255810,67840,4294969600,67840,4398046511170,132160,8589935680,17179870272,1,8796093284386,17592186306594,138469408,35184381050912,103100194848]),
([pw0,pw1,pw2,pw4,pw10,pw84,pw110,pw179,pw177],[20,24,64,68,72,9,25,76,80,205,221,3,165,217,225,84,88,29,105,125,141,1,5,13,17,21,41,45,49,73,77,81,93,97,101,109,113,117,129,133,157,209,213,229],[134218241,37,2199023256065,73,1099511628289,3,3,4398046511617,8228,16778256,131144,4215168,8796093022466,2101504,536875264,1073741844,2147483660,8228,8198,8388644,4294967332,8589934616,17179870224,262162,33555472,263184,34359738440,68719476746,131144,137438953544,268959874,67160192,824633804928,1,1574914,1148928]),
([pw0,pw1,pw2,pw4,pw10,pw84,pw110,pw177,pw180],[92,96,100,28,104,3,20,108,1,17,5,9,25,33,112,116,13,21,29,41,125,53,57,61,65,69,77,81,85,89,97,101,105,109,113,117,121,137,213,233,237,241],[1281,67586,131588,266256,532704,274880004160,72,72,8388611,16777221,1281,1281,33554689,549755813897,1281,67108870,134217746,268437634,536872962,1099511627786,67586,1073741844,2147484164,4294967812,131588,16932,8589938704,17179873296,34359738392,266256,68720566432,2199027458184,549024,137438986280,1097760,64]),
([pw0,pw1,pw2,pw4,pw10,pw84,pw110,pw114,pw177],[16,24,120,124,128,136,3,132,1,245,52,5,9,144,17,25,21,37,57,101,109,125,140,148,13,45,53,61,65,73,77,81,89,93,97,113,117,121,133,249,253,257,261,265],[2308,16781320,81936,549755847328,131777,35652226,4327104,67379904,134217740,268435476,2308,2308,1099511627782,2308,536871172,1073741848,2147483688,4105,4294967306,4168,8589938696,17179869232,524305,2199023255570,541712,81936,1048609,34359738402,1082400,68719509536,3,3,4535485472769,1,8796095119426,274886566976]),
([pw0,pw1,pw2,pw4,pw10,pw84,pw110,pw177,pw181],[16,28,152,156,164,168,160,269,1,52,172,5,9,3,176,17,25,49,37,101,105,109,125,241,13,45,53,61,65,69,73,77,81,89,93,97,113,245,261,273,277,281],[2308,16781320,549755846864,137439019232,270529,33694912,75497666,287424,134217740,268435476,2308,2308,536871172,1073741830,2308,2147483672,4294967336,4105,8589938696,17179869194,20488,34359738416,524305,1081360,1048594,557584,2097185,68719542304,1099511627810,2163232,274882102273,3,3,2199031776258,4351488,1]),
([pw0,pw1,pw2,pw4,pw10,pw84,pw110,pw177,pw182],[24,28,180,184,192,196,140,188,269,3,200,1,41,5,9,17,25,21,45,69,89,113,121,204,13,37,53,61,65,73,77,81,85,97,101,109,129,245,273,281,285,289,293],[10244,16793608,274877940112,137439019424,33560448,263041,67109762,263104,134217740,268435476,10244,10244,524293,536870918,526404,1073741848,2147483688,4294984712,1048585,1099511627786,1065032,8589934640,17179901968,2199023255569,131090,163920,34359803936,2097185,4398046511138,2162784,4199937,618475295746,12588608,3,3,1])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD10 : List StD := [
([pw1,pw2,pw4,pw10,pw84,pw178,pw110,pw177,pw180],[112,108,208,217,212,161,216,220,148,13,17,177,25,165,21,53,73,93,5,37,57,69,105,113,117,137,157,169,173,181,185,193,201,213,297,3],[524,262192,8240,8240,8240,2097200,65584,65584,134217740,268435468,524,524,524,131084,131084,6208,536871042,17536,4195456,17536,17179870337,1073741890,6208,8390720,16777281,6208,3,258,2147483651,259,8589967616,33027,3,34394341377,67633153,4294967297]),
([pw0,pw1,pw2,pw4,pw10,pw178,pw110,pw114,pw177],[48,52,224,228,232,148,236,1,5,17,132,9,21,25,16,29,41,57,89,121,189,301,13,61,65,77,81,97,201,233,237,253,257,265,305,309],[388,4196360,4624,41024,16384,3145729,66563,132128,8388620,16777236,388,388,2147483653,388,536870948,33554456,67108936,264202,262153,17179871242,1073741864,134217808,4624,4294967313,530,4624,41024,2097217,8258,34359738464,1572867,1025,268959778,16384,8589934625,196642]),
([pw0,pw1,pw2,pw4,pw10,pw178,pw110,pw177,pw181],[52,160,148,240,244,41,248,37,161,313,256,89,129,169,17,49,113,153,193,140,252,5,13,25,57,61,69,73,93,105,145,149,157,165,173,245,261,277,281,317,321],[1073741834,2147483666,131202,131202,34359738371,4294967426,262150,163,33554456,2097416,8589934856,265,67109128,134217740,41,4202512,17179877392,2065,10256,268435476,2065,16960,577,536871488,580,16481,549755817985,9536512,137438954500,66593,68719480833,1099511631877,35,274878169092,557089,16777221]),
([pw0,pw1,pw2,pw4,pw10,pw84,pw110,pw183,pw177],[52,132,260,264,268,48,205,29,37,217,221,325,148,272,5,13,21,329,0,17,25,33,41,49,73,77,81,93,97,113,117,149,153,197,201,213,245,257,261,265,3],[322,2147483654,322,4294967362,322,322,68719476739,34359738434,33284,525320,1048720,4196353,8519712,286721,16801792,33554444,67108884,517,33284,1099511627781,134218244,268435480,1033,137438953512,65545,66568,145,536870960,145,1073741968,133153,2097153,274877908993,8589934625,549755818016,17179873281]),
([pw184,pw0,pw1,pw2,pw4,pw10,pw84,pw110,pw177],[48,276,280,284,288,292,140,148,17,25,45,165,5,13,89,21,201,29,41,57,61,65,73,77,81,93,97,117,133,145,149,181,185,213,261,3],[1027,6148,24584,33040,131616,3,129,34360328384,536870918,1073741834,274,546,1027,1027,8589935618,1048588,2097172,6148,6148,69,4196356,8388632,16777256,24584,16393,33562632,67108912,2147484048,81,33040,4294967968,97,134218272,193,17448632448,65]),
([pw0,pw1,pw2,pw4,pw10,pw84,pw110,pw177,pw185],[148,296,300,304,308,1,17,5,9,25,160,312,129,21,29,41,57,89,197,140,316,13,33,37,61,65,69,77,81,97,105,113,157,201,233,237,245,261,277,281,305],[162,2097412,8264,16912,36865,4303621120,66561,68719477761,16777222,33554442,162,162,67108898,17179869187,162,134217740,268435476,1099511628037,131332,34359738373,131333,536870936,73,1073741896,8264,1048649,529,2147484176,274877906961,16912,137438957569,36867,4194305,549755881473,788481,8589934593]),
([pw186,pw0,pw1,pw2,pw4,pw10,pw84,pw110,pw177],[148,328,332,336,340,5,21,29,89,129,41,320,344,348,9,197,201,0,8,12,24,140,324,1,17,25,37,53,57,61,65,69,77,81,97,105,113,141,157,261,309,333],[4196353,131107,2309,262217,524433,1537,3178497,268435457,8388642,16644,16777288,33554576,1537,274945060864,134225921,536870918,1073741834,50,35,2147483682,65539,4294967308,8589934612,261,16644,2199023255557,17179869208,73,34359738440,73,145,68719476880,1099511627793,549755814401,1537,137439023105]),
([pw0,pw1,pw2,pw4,pw10,pw84,pw178,pw110,pw177,pw182],[148,352,356,5,13,21,29,37,188,41,360,364,48,1,17,89,140,25,69,113,137,141,153,157,281,56,9,61,73,105,161,169,173,177,245,285,293,305,313,3],[8330,67109012,4210848,4325568,769,17179869441,8388992,549755814273,8388992,134217742,1073741834,8202,8202,8202,262154,268435467,262154,2147483668,4294967316,137438953493,32789,32788,34359738389,32788,283467841632,1569,17440,536871968,17441,17440,2625,133184,526400,68719478849,526400,256,1053185,18874881,66049,1052673,18874369,33619969,4097,1,4096]),
([pw0,pw1,pw2,pw4,pw10,pw84,pw110,pw179,pw177,pw181],[172,368,372,13,5,21,29,45,160,376,380,1,129,88,17,217,76,25,9,49,109,125,157,281,16,148,176,384,73,81,93,101,105,113,117,133,161,169,177,205,209,213,221,229,261],[549755816080,262282,1099511644320,131268,4198784,257,1,2199023255936,4194688,32794,4466765987888,133188,6672,8796093022737,2576,268435984,2576,137438953482,536870926,32778,32779,262154,1073741834,32778,274877907044,2147488800,4294968353,17440,17440,17440,1048644,8589934661,131140,17179869252,1048644,2625537,17592202891264,73728,8192,256,8396801,2621441,34368135168,234881024,65536]),
([pw0,pw1,pw2,pw4,pw10,pw84,pw179,pw177,pw182],[140,388,392,396,400,1,188,404,9,17,25,5,21,33,157,24,88,148,13,29,49,41,61,65,73,77,81,85,93,97,101,109,117,125,129,137,281,337],[2082,262404,4616,525328,2121920,32832,137438969920,1065025,4194310,8388618,2082,2082,2082,16777250,35,33554444,67108884,134218116,262404,268435716,261,536870936,1073742344,4616,4616,4616,2147484688,525328,4294968336,1041,139393,85899419776,8589942913,34359934977,1048641,32768]),
([pw0,pw1,pw2,pw4,pw10,pw84,pw110,pw177,pw187],[140,408,412,416,205,29,420,424,13,165,221,225,88,217,341,125,241,148,316,5,17,21,25,45,57,73,77,81,93,97,101,109,117,157,197,201,209,245,345],[8388625,16401,68719476753,274877906961,8589934609,16401,16401,137438953473,8450,1049604,4194344,527040,641,33555072,641,67108870,134217738,8450,259,268443650,259,536870924,1073742852,1029,2098180,262149,2147483688,41,4294967336,41,34881,16848960,133185,102401,17179869185,34359742465]),
([pw188,pw0,pw1,pw2,pw10,pw84,pw110,pw177],[428,432,436,440,444,1,5,9,25,100,316,448,33,452,13,29,101,241,297,17,57,61,69,81,85,89,105,109,113,121,125,233,237,273,349,353,357,3],[513,98,16516,33032,594960,67175424,1537,98,16516,33032,8590202896,17180133376,2561,2097158,98,98,4194338,2147483651,8388620,16777364,33554564,4294967301,134217992,268435720,34359738377,139049578512,1179665,68719616001]),
([pw0,pw1,pw2,pw4,pw10,pw84,pw110,pw114,pw177,pw180],[148,456,460,5,108,21,29,53,13,132,468,1,464,121,472,125,116,9,17,25,241,3,104,140,476,33,57,65,69,89,105,113,117,173,213,233,237,301,313,341,345,361,365,369],[2186,549755945344,262308,1099512152256,8849,17179869824,641,513,1,2199023255562,134217742,2058,2058,268435466,2058,34359738379,2058,4398046511396,8804682957120,17,536908032,2101249,68719481089,135424,274877906980,53,1073741860,37,262180,2098212,8273,139586469952,4210753,4294983745,541760,17,33554433,1056785,8209,16,8454145,99328,68158465,16778241,512]),
([pw0,pw1,pw2,pw4,pw10,pw84,pw110,pw180,pw182],[140,480,484,1,17,112,488,57,173,341,492,109,361,28,137,116,9,13,25,41,53,65,89,101,141,241,281,313,345,357,365,373,377,3],[11,1049089,21,268435969,8590459393,2147484161,8193,4294967937,4106,2097158,4106,4106,11,4106,11,1073741844,131392,4194624,321,65856,449,134217748,8388628,21,536870964,21,265216,3073,3104,3201,49153,83886112,33554561,16417,8193,161]),
([pw189,pw0,pw1,pw2,pw4,pw10,pw84,pw110,pw177],[140,476,496,500,504,508,9,5,17,25,49,41,301,0,4,8,12,112,512,516,21,37,53,61,65,73,77,81,93,97,117,181,185,245,261,305,381],[2097153,8325,16457,33041,66081,786433,5121,131075,68719476741,73,273,545,2051,5121,8594128897,8388620,16777236,164,2054,133,33554564,67108888,134217768,34359738442,73,268435528,536870960,2147483666,273,1048848,4294967330,545,1073742368,5121,17179871234,1027]),
([pw123,pw0,pw1,pw4,pw10,pw84,pw110,pw114,pw177],[140,520,524,148,528,37,532,5,57,109,165,124,536,17,25,101,245,133,45,65,97,233,309,381,385,389],[65569,1154,40964,16912,2112,2049,2049,135432,8388611,37,529,65569,262177,65569,265,524294,1154,1154,1027,131,2097162,1048596,40964,32773,8197,16777228,16912,529,16401,4194328,65,65,135432,33554433,65,4361]),
([pw123,pw0,pw1,pw4,pw10,pw84,pw110,pw177],[140,540,544,9,245,548,552,556,121,560,17,25,1,217,564,57,269,305,389,532,13,21,45,53,65,73,93,97,117,169,173,393,397,401,405,409,413,417,421,425,429,3],[1048607,8206,536870926,1073741838,8462,8207,67108878,2147487793,66641,67729,131859,4299423761,2199031693329,16777312,8589934752,802,17179873313,33558560,134217920,34359739458,68719477825,2098240,137438955650,274877909121,268437632,131841,549755814656,1099512463361]),
([pw0,pw1,pw2,pw4,pw10,pw84,pw114,pw177,pw182],[140,433,200,568,572,576,29,221,580,5,13,137,217,37,53,121,125,269,441,28,584,17,21,25,33,73,77,81,93,97,101,109,117,245,437],[8589934595,17179869187,131075,131075,8195,8195,16387,16387,5128,2097296,8388704,294916,2817,33555200,769,67108888,134217768,5128,2057,268439560,1033,536870960,1073741844,145,4194448,145,2147483684,97,4294967392,97,16777221,294916,65541,526337,65541,1048577]),
([pw0,pw1,pw2,pw4,pw10,pw84,pw110,pw177,pw190],[140,433,588,592,161,200,596,217,144,13,125,177,37,165,269,445,453,8,600,5,17,25,33,45,49,53,57,73,93,109,121,133,169,173,245,277,437,449,3],[17179869187,68719476739,16387,16387,4099,8388611,33554435,4099,644,524312,8216,8216,25,134217752,25,4294967428,8589934724,644,517,268435588,274877906949,2099264,1073774624,137438954497,2147549440,1441793,536871008,2113,34359738688,2113,1057,32808,4194337,66817,16777217,67109121]),
([pw191,pw0,pw1,pw2,pw4,pw10,pw84,pw110,pw177],[476,148,140,245,604,608,612,93,121,129,137,9,269,1,17,25,57,61,65,77,81,97,113,125,233,253,257,309,385,393,401,457],[15,3,131,3,3,770,1027,4,536879132,2189,20524,36940,15,8389645,2147549198,131089,262192,1073741904,3,33554449,16777234,524321,1048641,131,2177,131,2097248,3,67108897,268435490,3,4194369,134217794,771,771,1031]),
([pw192,pw0,pw1,pw2,pw4,pw10,pw84,pw110,pw177],[140,616,620,624,628,636,5,17,25,49,13,57,137,148,0,4,8,12,16,632,21,33,37,45,61,65,77,81,89,97,101,109,125,165,233,237,241,245,293,381,461],[8388609,16451,33797,65673,131345,2367489,4609,534529,549755813891,1099511627781,137,273,137443147777,4609,2081,16777222,33554442,82,8589934658,67,17179869218,67108876,134217748,268436484,1029,34359738404,536870936,1073741960,137,1048616,2147483920,273,274877906992,4294967809,68719478816,4609]),
([pw193,pw0,pw1,pw2,pw4,pw10,pw84,pw110,pw177],[148,140,640,644,648,652,45,21,73,89,113,133,137,9,25,41,141,656,1,17,61,65,77,81,97,125,241,245,253,257,277,285,401,3],[8589934659,261,521,145,1057,3,135171,67585,262470,8778,524498,17506,32835,167776322,67110915,1048588,2097172,4294967332,261,268435718,261,4194328,8388648,521,8714,2147483657,16777264,145,536871058,145,1057,17442,1073741857,36867,67585,2055])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD9 : List StD := [
([pw1,pw2,pw4,pw10,pw84,pw178,pw110,pw180,pw182],[148,5,13,25,17,325,112,140,53,668,217,660,672,37,465,29,165,313,664,41,69,113,137,1,9,105,161,169,173,177,221,341,361,365,369,377],[4294968326,1140850706,98314,589858,67843,1050626,8390658,1050626,8724152340,17448304652,525348,2147484933,4211716,17047556,263172,537002008,561,131841,33571344,8784,131600,4137,37129,6307848,45064,2101256,65,161,97,161,385,321,34359738497,16576,1,8384]),
([pw194,pw0,pw1,pw4,pw10,pw84,pw110,pw177],[140,688,676,469,49,544,680,17,165,217,148,260,684,485,5,57,313,477,13,37,41,45,73,93,169,173,181,221,473,481,489,493,497],[2057,262688,16777760,33554976,2080,2049,8389152,268435465,131081,131081,524297,2097177,536870921,134217924,20738,20738,275,4198662,65732,67109062,209,65732,1056770,1073741841,2147517444,8211,4294976518,33809]),
([pw0,pw1,pw2,pw4,pw10,pw84,pw110,pw177,pw195],[140,5,13,21,29,37,121,197,692,57,696,205,1,25,41,217,17,325,341,453,509,0,4,12,544,700,704,9,73,93,153,161,169,173,177,221,313,317,361,365,369,445,501,505,513,517,521],[6178,134479908,67624,1073750064,18528,2209,262177,2081,274877939718,36507222026,12306,135234,4398046511235,8796361458178,2101506,554050781196,1108101562388,163908,1048709,17592722915844,21004292,85899345944,2199023255880,35184372088969,590344,33555464,137438953808,1048721,70368744179216,75505680,16833,526144,16704,1665,1153,1]),
([pw188,pw0,pw1,pw2,pw10,pw84,pw110,pw114,pw177],[468,708,5,21,29,273,13,121,301,1,716,720,112,712,724,25,125,217,261,9,17,53,57,101,297,33,49,69,105,109,173,189,221,233,237,313,349,353,361,365,369,525,529,533,3],[3145768,4294967820,549756338248,34359771160,8650888,268501256,8392713,1048585,2199023256100,4398047035488,8796093055024,16777377,68719542560,16781345,2097185,274878038084,33300,262788,134226182,8708,8589942789,1100585369680,132288,132418,17592186045442,17179870273,536889488,65810,16402,137438969873,2147485698,33556482,264321,67108866,4194563,4198403]),
([pw123,pw0,pw1,pw4,pw10,pw84,pw110,pw177,pw180],[676,5,13,17,85,389,25,53,728,57,148,125,140,121,165,217,540,732,1,21,101,109,213,241,544,552,9,65,69,93,105,113,117,169,173,233,305,313,345,485,489,3],[71303300,49158,8590983180,17181966404,40980,34852,545260036,16842757,262531,524425,274877907073,1169,4196512,1153,1025,134217995,16706,24594,268435746,34359739139,262403,137438953545,1048601,1073741865,524809,2199056809993,549757912144,1101659111520,4295098945,131137,10288,8389137,68719543313,4641,6177,4097]),
([pw196,pw0,pw1,pw4,pw10,pw84,pw110,pw177],[676,140,736,740,245,544,17,161,217,13,177,37,165,269,541,21,25,45,53,73,85,93,117,169,173,417,433,537,545,549],[2067,800,8388897,16777504,800,546,2097441,67108883,8211,8211,2067,131091,262163,134217925,4228,4228,134,524421,66633,1065029,75,805339201,33554444,1034,4195337,14,16397,11]),
([pw0,pw197,pw1,pw2,pw4,pw10,pw84,pw110,pw177],[148,748,760,5,21,33,752,13,29,301,756,45,57,1,25,133,112,744,9,41,49,341,4,12,544,17,205,209,229,233,277,345,361,369,513,553,557],[1,67119112,2361472,167774224,2147502336,524321,3148288,36865,139274,21233792,66640,8405252,524321,197122,36865,4294967434,1114,24840,11,268435982,536870915,1232,8589934980,35,34359739012,17179873281,1360,35,1616,81,35,1049348,1073741829,35,36897,68719476741])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD8 : List StD := [
([pw188,pw123,pw0,pw1,pw10,pw84,pw110,pw177],[5,13,17,29,85,273,389,561,1,25,121,217,9,21,53,57,101,109,125,241,297,305,397,69,73,93,105,113,117,173,221,313,349,357,425,429,485,489,505,525,533,565,569],[69638,24612,1073742085,2147484172,2162708,71303236,41092,1052706,2307,537001994,3090,264258,34078850,549755814177,1099511628328,3145776,4299161696,49312,777,1297,2199031644225,274894684289,68719607832,137573171272,4398314946696,263248,17180393616,42949673152])]
def ptopD7 : List StD := []
theorem ptopI7 : LevelN true ptopT 7 ptopD7 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC8x0 : levelOK true ptopT ptopt 7 (ptopD7.map Prod.fst) ((ptopD8.drop (0*32)).take 32) = true := by decide +kernel
theorem ptopI8 : LevelN true ptopT 8 ptopD8 := levelStep ptopB ptopW ptopI7 (chunks 32 ptopD8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC8x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC9x0 : levelOK true ptopT ptopt 8 (ptopD8.map Prod.fst) ((ptopD9.drop (0*32)).take 32) = true := by decide +kernel
theorem ptopI9 : LevelN true ptopT 9 ptopD9 := levelStep ptopB ptopW ptopI8 (chunks 32 ptopD9 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC9x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC10x0 : levelOK true ptopT ptopt 9 (ptopD9.map Prod.fst) ((ptopD10.drop (0*32)).take 32) = true := by decide +kernel
theorem ptopI10 : LevelN true ptopT 10 ptopD10 := levelStep ptopB ptopW ptopI9 (chunks 32 ptopD10 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC10x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem ptopC11x0 : levelOK true ptopT ptopt 10 (ptopD10.map Prod.fst) ((ptopD11.drop (0*32)).take 32) = true := by decide +kernel
theorem ptopI11 : LevelN true ptopT 11 ptopD11 := levelStep ptopB ptopW ptopI10 (chunks 32 ptopD11 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact ptopC11x0
  ))
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

end PEqualNP.Outside.L_meta_14692

theorem PEqualNP.Outside.L_meta_14692 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 0, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact PEqualNP.Outside.L_meta_14692.replaceShort gates o fit correct
