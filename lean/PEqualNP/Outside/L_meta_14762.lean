import PEqualNP.Defs

-- The live-set and restriction lemmas follow L-meta-10554, L-meta-10802, L-meta-1674, L-meta-670 and L-meta-1667.
-- The rectangle argument follows L-meta-8459.
namespace PEqualNP.Outside.L_meta_14762
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


def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[
    ⟨.or, [5, 6]⟩,
    ⟨.or, [0, 6]⟩,
    ⟨.or, [0, 2]⟩,
    ⟨.or, [4, 6]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.or, [2, 12]⟩,
    ⟨.or, [4, 13]⟩,
    ⟨.and, [3, 9]⟩,
    ⟨.and, [10, 8]⟩,
    ⟨.and, [1, 11]⟩,
    ⟨.and, [14, 7]⟩,
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
def pw83 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000
def pw84 : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
def pw85 : Nat := 0x555500005555000055550000555500005555000055550000555500005555
def pw86 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
def pw87 : Nat := 0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc
def pw88 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0fff0
def pw89 : Nat := 0xfc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc00fc
def pw90 : Nat := 0xf0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c
def pw91 : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
def pw92 : Nat := 0x4444444444444444444444444444444444444444444444444444444444444444
def pw93 : Nat := 0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc
def pw94 : Nat := 0x11111111000000001111111100000000111111110000000011111111
def pw95 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00
def pw96 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000
def pw97 : Nat := 0x5555555500000000555555550000000055555555000000005555555500000000
def pw98 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00
def pw99 : Nat := 0xf0000000f0000000f0000000f0000000f0000000f0000000f0000000f
def pw100 : Nat := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0
def pw101 : Nat := 0x5050505050505050505050505050505050505050505050505050505050505050
def pw102 : Nat := 0xffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaaffffffffaaaaaaaa
def pw103 : Nat := 0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa
def pw104 : Nat := 0x3030303030303030303030303030303030303030303030303030303030303030
def pw105 : Nat := 0xffffccccffffccccffffccccffffccccffffccccffffccccffffccccffffcccc
def pw106 : Nat := 0xffffffffccccccccffffffffccccccccffffffffccccccccffffffffcccccccc
def pw107 : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0
def pw108 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0
def pw109 : Nat := 0xfffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0fffffffff0f0f0f0
def pw110 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0
def pw111 : Nat := 0xffffffffff00ff00ffffffffff00ff00ffffffffff00ff00ffffffffff00ff00
def pw112 : Nat := 0xffffffffffff0000ffffffffffff0000ffffffffffff0000ffffffffffff0000
def pw113 : Nat := 0xeeeeeeee00000000eeeeeeee00000000eeeeeeee00000000eeeeeeee
def pw114 : Nat := 0xecececececececececececececececececececececececececececececececec
def pw115 : Nat := 0xffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0
def pw116 : Nat := 0xffffa0a0ffffa0a0ffffa0a0ffffa0a0ffffa0a0ffffa0a0ffffa0a0ffffa0a0
def pw117 : Nat := 0xffffffffa0a0a0a0ffffffffa0a0a0a0ffffffffa0a0a0a0ffffffffa0a0a0a0
def pw118 : Nat := 0x3333333322222222333333332222222233333333222222223333333322222222
def pw119 : Nat := 0xf0f0f0f0fafafafaf0f0f0f0fafafafaf0f0f0f0fafafafaf0f0f0f0fafafafa
def pw120 : Nat := 0xffffffff30303030ffffffff30303030ffffffff30303030ffffffff30303030
def pw121 : Nat := 0xfff00000fff00000fff00000fff00000fff00000fff00000fff00000fff0
def pw122 : Nat := 0xaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafaaafa
def pw123 : Nat := 0xff00f000ff00f000ff00f000ff00f000ff00f000ff00f000ff00f000ff00f0
def pw124 : Nat := 0xaaaafafaaaaafafaaaaafafaaaaafafaaaaafafaaaaafafaaaaafafaaaaafafa
def pw125 : Nat := 0xccccccccfcfcfcfcccccccccfcfcfcfcccccccccfcfcfcfcccccccccfcfcfcfc
def pw126 : Nat := 0x22f222f222f222f222f222f222f222f222f222f222f222f222f222f222f222f2
def pw127 : Nat := 0x2222f2f22222f2f22222f2f22222f2f22222f2f22222f2f22222f2f22222f2f2
def pw128 : Nat := 0xf000f0aafaaafa00f000f0aafaaafa00f000f0aafaaafa00f000f0aafaaafa
def pw129 : Nat := 0xf0f0aaaafafa0000f0f0aaaafafa0000f0f0aaaafafa0000f0f0aaaafafa
def pw130 : Nat := 0x3333303033333030333330303333303033333030333330303333303033333030
def pw131 : Nat := 0x55555555000000005555555500000000555555550000000055555555
def pw132 : Nat := 0xffff000000000000ffff000000000000ffff000000000000ffff
def pw133 : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
def pw134 : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
def pw135 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0
def pw136 : Nat := 0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc
def pw137 : Nat := 0xf4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4f4
def pw138 : Nat := 0xffff4444ffff4444ffff4444ffff4444ffff4444ffff4444ffff4444ffff4444
def pw139 : Nat := 0xdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdc
def pw140 : Nat := 0xffffffff50505050ffffffff50505050ffffffff50505050ffffffff50505050
def pw141 : Nat := 0xeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaea
def pw142 : Nat := 0xffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0ffc0
def pw143 : Nat := 0xffffc0c0ffffc0c0ffffc0c0ffffc0c0ffffc0c0ffffc0c0ffffc0c0ffffc0c0
def pw144 : Nat := 0xffffffffc0c0c0c0ffffffffc0c0c0c0ffffffffc0c0c0c0ffffffffc0c0c0c0
def pw145 : Nat := 0xfffffcfcfffffcfcfffffcfcfffffcfcfffffcfcfffffcfcfffffcfcfffffcfc
def pw146 : Nat := 0xfcfc0000fcfc0000fcfc0000fcfc0000fcfc0000fcfc0000fcfc0000fcfc
def pw147 : Nat := 0xfffffffffcfcfcfcfffffffffcfcfcfcfffffffffcfcfcfcfffffffffcfcfcfc
def pw148 : Nat := 0xfcfcfcfc00000000fcfcfcfc00000000fcfcfcfc00000000fcfcfcfc
def pw149 : Nat := 0xaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaeae
def pw150 : Nat := 0xffffffff0c0c0c0cffffffff0c0c0c0cffffffff0c0c0c0cffffffff0c0c0c0c
def pw151 : Nat := 0xbabababababababababababababababababababababababababababababababa
def pw152 : Nat := 0xffff3030ffff3030ffff3030ffff3030ffff3030ffff3030ffff3030ffff3030
def pw153 : Nat := 0xaaaaeeeeaaaaeeeeaaaaeeeeaaaaeeeeaaaaeeeeaaaaeeeeaaaaeeeeaaaaeeee
def pw154 : Nat := 0xf0f0fcfcf0f0fcfcf0f0fcfcf0f0fcfcf0f0fcfcf0f0fcfcf0f0fcfcf0f0fcfc
def pw155 : Nat := 0xf0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c0f0f0f0f0c0c0c0c
def pw156 : Nat := 0xf0f0f0f0fcfcfcfcf0f0f0f0fcfcfcfcf0f0f0f0fcfcfcfcf0f0f0f0fcfcfcfc
def pw157 : Nat := 0xccccfcfcccccfcfcccccfcfcccccfcfcccccfcfcccccfcfcccccfcfcccccfcfc
def pw158 : Nat := 0xaaaaaaaafafafafaaaaaaaaafafafafaaaaaaaaafafafafaaaaaaaaafafafafa
def pw159 : Nat := 0xfefefefe00000000fefefefe00000000fefefefe00000000fefefefe
def pw160 : Nat := 0xaeaeaeae00000000aeaeaeae00000000aeaeaeae00000000aeaeaeae
def pw161 : Nat := 0xbaba0000baba0000baba0000baba0000baba0000baba0000baba0000baba
def pw162 : Nat := 0xcccccccceeeeeeeecccccccceeeeeeeecccccccceeeeeeeecccccccceeeeeeee
def pw163 : Nat := 0xffff0000ffffaaaaffff0000ffffaaaaffff0000ffffaaaaffff0000ffffaaaa
def pw164 : Nat := 0xffffffffffccffccffffffffffccffccffffffffffccffccffffffffffccffcc
def pw165 : Nat := 0xfac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8fac8
def pw166 : Nat := 0xcccc0000eeee0000cccc0000eeee0000cccc0000eeee0000cccc0000eeee
def pw167 : Nat := 0x8888888888888888888888888888888888888888888888888888888888888888
def pw168 : Nat := 0xff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88ff88
def pw169 : Nat := 0xffff8888ffff8888ffff8888ffff8888ffff8888ffff8888ffff8888ffff8888
def pw170 : Nat := 0xffffffff88888888ffffffff88888888ffffffff88888888ffffffff88888888
def pw171 : Nat := 0x333333333333333300000000000000003333333333333333
def pw172 : Nat := 0x30003000300030003000300030003000300030003000300030003000300030
def pw173 : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
def pw174 : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff
def pw175 : Nat := 0xaaaa0000aaaa00000000000000000000aaaa0000aaaa
def pw176 : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000
def pw177 : Nat := 0xfffffffffffffffff0f0f0f0f0f0f0f0fffffffffffffffff0f0f0f0f0f0f0f0
def pw178 : Nat := 0xffffffffffffffffff00ff00ff00ff00ffffffffffffffffff00ff00ff00ff00
def pw179 : Nat := 0xffffffffffffffffffff0000ffff0000ffffffffffffffffffff0000ffff0000
def pw180 : Nat := 0xfffff0f0fffff0f00000000000000000fffff0f0fffff0f0
def pw181 : Nat := 0x3333333333333333303030303030303033333333333333333030303030303030
def pw182 : Nat := 0xffff0000ffff0000f0f00000f0f00000ffff0000ffff0000f0f00000f0f0
def pw183 : Nat := 0xffffffffffffffffffffff00ffffff00ffffffffffffffffffffff00ffffff00
def pw184 : Nat := 0xffffff00ffffff000000000000000000ffffff00ffffff00
def pw185 : Nat := 0xffff0000ffff0000ff000000ff000000ffff0000ffff0000ff000000ff00
def pw186 : Nat := 0x5555555555555555555500005555000055555555555555555555000055550000
def pw187 : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
def pw188 : Nat := 0x5500550055005500000000000000000055005500550055
def pw189 : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
def pw190 : Nat := 0xffffffffffffffffffffffffffffffff
def pw191 : Nat := 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000
def pw192 : Nat := 0x55555555555555555555555555555555
def pw193 : Nat := 0x3333000033330000333300003333
def pw194 : Nat := 0x3333333333333333333333333333333300000000000000000000000000000000
def pw195 : Nat := 0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000
def pw196 : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
def pw197 : Nat := 0xffffffffffffffffffffffffffffffffaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def pw198 : Nat := 0x5555555555555555555555555555555500000000000000000000000000000000
def pw199 : Nat := 0xffffffffffffffffccccccccccccccccffffffffffffffffcccccccccccccccc
def pw200 : Nat := 0xffffffffffffffffffffffffffffffffcccccccccccccccccccccccccccccccc
def pw201 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000
def pw202 : Nat := 0xffffffffffffffff00000000000000000000000000000000
def pw203 : Nat := 0xffffffffffffffffffffffffffffffffeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
def pw204 : Nat := 0x3333333333333333333333333333333322222222222222222222222222222222
def pw205 : Nat := 0xddddddddddddddddddddddddddddddddcccccccccccccccccccccccccccccccc
def pw206 : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffcccccccccccccccc
def pw207 : Nat := 0x5555555555555555555555555555555544444444444444444444444444444444
def pw208 : Nat := 0xffff0000ffff0000ffff0000ffff0000cccc0000cccc0000cccc0000cccc
def pw209 : Nat := 0xffffffffffffffff0000000000000000cccccccccccccccc
def pw210 : Nat := 0xbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
def pw211 : Nat := 0xffffffffffffffff3333333333333333ffffffffffffffff0000000000000000
def pw212 : Nat := 0x3333333333333333333333333333333333333333333333330000000000000000
def pw213 : Nat := 0xccccccccccccccccffffffffffffffffcccccccccccccccccccccccccccccccc
def pw214 : Nat := 0xffff0000ffff0000ffff0000ffff0000eeee0000eeee0000eeee0000eeee
def pw215 : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000cccc0000cccc
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
def p4_T : Nat := 0xfefefeeefefafca8fefefeeefefafca8fefefeeefefafca8fefefeeefefafca8
def p4_R : List Nat := [0, 1, 2, 3, 4, 5]
def p4_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,2,10),(4,1,17),(5,1,33)]
theorem p4_B : baseOK p4_T p4_R p4_E = true := by decide +kernel
def p4_Z : List SliceD := [(pw3,8,[0, 1, 2, 4, 5])]
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
([pw0,pw1,pw2,pw4,pw10,pw83],[0],[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])]
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
def p6_Z : List SliceD := [(pw84,4,[1, 2, 3])]
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
def p7_Z : List SliceD := [(pw85,4,[1, 2, 3]),(pw6,4,[0, 1, 3, 4]),(pw3,4,[0, 1, 2, 4]),(pw10,5,[0, 1, 2, 3]),(pw7,5,[1, 2, 3, 0])]
theorem p7_Y : ∀ s ∈ p7_Z, SliceN true p7_R p7_T s := by
  unfold p7_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p7_B p1_B p1_L (by decide +kernel),mkSlice (w:=0) p7_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p7_B p5_B p5_L (by decide +kernel),mkSlice (w:=16) p7_B p6_B p6_L (by decide +kernel),mkSlice (w:=0) p7_B p2_B p2_L (by decide +kernel),by simp⟩
def p7_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[])]
def p7_t : Tabs := (p7_C.map (mkCut true p7_Z),[(3,2),(17,16),(21,20),(25,24),(12,8),(6,4),(6,2),(12,4),(10,8),(10,2),(7,4),(12,5),(3,5),(3,1),(6,20),(17,1),(6,18),(21,5),(17,9),(12,9),(6,0),(17,5),(11,8),(3,9),(10,24),(10,18),(25,9),(10,0),(12,20),(12,0),(12,1),(17,0),(10,16),(22,2),(7,0),(6,16),(12,16)],[],[[]])
theorem p7_W : TabsP true p7_R p7_T p7_t := ⟨cutsGood p7_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p7_D6 : List StD := [
([pw0,pw1,pw2,pw4,pw10],[0,1,12,3,4,8,5,17,25,29,9,13,21,33,37],[67,1027,2051,67,4504,25128,5,952,5,5])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p7_D5 : List StD := [
([pw0,pw1,pw2,pw19,pw4,pw10],[1,37,21,61,9,25,29,8,5,17,41,45,49,53,57,65,69,73,3],[1029,17,257,2051,17,4132,8192,70,16396,512,66,32808,262274,65544,131082]),
([pw86,pw0,pw1,pw2,pw4,pw10],[5,29,61,1,17,37,21,12,16,25,45,53,57,73,77,81,85],[9,2048,512,34,388,9,16401,1027,9,32848,34,4164,34,65556,8198]),
([pw0,pw1,pw2,pw4,pw20,pw10],[1,25,33,61,13,17,37,4,5,29,53,77,85,89,93,97,101,105,3],[8197,2051,17,257,17,38,16452,1024,32780,34,262274,4106,512,65608,131080]),
([pw87,pw0,pw1,pw2,pw4,pw10],[5,17,61,1,25,29,33,12,16,37,45,53,73,77,85,97,109],[9,2048,18,512,388,9,8195,1057,9,18,65632,32836,18,16390,4132]),
([pw0,pw1,pw2,pw4,pw88,pw10],[21,1,61,29,53,4,9,17,69,25,33,45,57,77,113],[17,8322,2058,66,66,17,1025,17,4101,40,512,388,32,16396,260])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p7_D4 : List StD := [
([pw89,pw0,pw1,pw2,pw10],[1,25,37,69,109,61,117,41,45,53,121,125,129],[261,532,70,44,145,1027,2057,82,4120,42]),
([pw90,pw0,pw1,pw4,pw10],[1,25,37,61,81,117,53,77,121,125,133,137,141,145],[131,82,38,1034,2065,261,521,52,4120,8204])]
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
def p8_T : Nat := 0xfeeefac8feeefac8feeefac8feeefac8feeefac8feeefac8feeefac8feeefac8
def p8_R : List Nat := [0, 1, 2, 3, 4]
def p8_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,1,9),(4,1,17)]
theorem p8_B : baseOK p8_T p8_R p8_E = true := by decide +kernel
def p8_Z : List SliceD := [(pw6,5,[0, 1, 4, 3])]
theorem p8_Y : ∀ s ∈ p8_Z, SliceN true p8_R p8_T s := by
  unfold p8_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p8_B p2_B p2_L (by decide +kernel),by simp⟩
def p8_C : List (Nat × List Nat) := [(0,[])]
def p8_t : Tabs := (p8_C.map (mkCut true p8_Z),[(9,8),(6,4),(3,2),(3,1),(6,2),(21,20)],[],[[]])
theorem p8_W : TabsP true p8_R p8_T p8_t := ⟨cutsGood p8_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p8_D5 : List StD := [
([pw0,pw1,pw2,pw4,pw10],[0,1,5,17,9,13,21],[54,75,17,3,33,5,5,9,9,1])]
def p8_D4 : List StD := []
theorem p8_I4 : LevelN true p8_T 4 p8_D4 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p8_C5x0 : levelOK true p8_T p8_t 4 (p8_D4.map Prod.fst) ((p8_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p8_I5 : LevelN true p8_T 5 p8_D5 := levelStep p8_B p8_W p8_I4 (chunks 32 p8_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p8_C5x0
  ))
theorem p8_L : LowN true p8_R p8_T 6 := lowSearch p8_B p8_I5 (by decide +kernel)
def p9_T : Nat := 0xfffefeeefffefeeefffefeeefffefeeefffefeeefffefeeefffefeeefffefeee
def p9_R : List Nat := [0, 1, 2, 3, 4]
def p9_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,8,12),(3,4,12),(4,4,20)]
theorem p9_B : baseOK p9_T p9_R p9_E = true := by decide +kernel
def p9_Z : List SliceD := [(pw84,5,[1, 2, 3, 4])]
theorem p9_Y : ∀ s ∈ p9_Z, SliceN true p9_R p9_T s := by
  unfold p9_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p9_B p6_B p6_L (by decide +kernel),by simp⟩
def p9_C : List (Nat × List Nat) := [(0,[])]
def p9_t : Tabs := (p9_C.map (mkCut true p9_Z),[(1,0),(2,0)],[],[[]])
theorem p9_W : TabsP true p9_R p9_T p9_t := ⟨cutsGood p9_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p9_D5 : List StD := [
([pw0,pw1,pw2,pw4,pw10],[0,1,5],[7,3,3,3,5,5,5,1,1,1])]
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
theorem p9_L : LowN true p9_R p9_T 6 := lowSearch p9_B p9_I5 (by decide +kernel)
def p10_T : Nat := 0xfffefeeefff8fac8fffefeeefff8fac8fffefeeefff8fac8fffefeeefff8fac8
def p10_R : List Nat := [0, 1, 2, 3, 4, 5]
def p10_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,1,9),(4,4,20),(5,1,33)]
theorem p10_B : baseOK p10_T p10_R p10_E = true := by decide +kernel
def p10_Z : List SliceD := [(pw84,7,[1, 2, 3, 4, 5]),(pw5,7,[0, 3, 2, 4, 5]),(pw6,7,[3, 0, 1, 5, 4]),(pw3,7,[2, 1, 0, 5, 4]),(pw7,6,[0, 1, 2, 3, 5]),(pw10,6,[2, 3, 0, 1, 5])]
theorem p10_Y : ∀ s ∈ p10_Z, SliceN true p10_R p10_T s := by
  unfold p10_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p10_B p7_B p7_L (by decide +kernel),mkSlice (w:=0) p10_B p7_B p7_L (by decide +kernel),mkSlice (w:=0) p10_B p7_B p7_L (by decide +kernel),mkSlice (w:=0) p10_B p7_B p7_L (by decide +kernel),mkSlice (w:=0) p10_B p8_B p8_L (by decide +kernel),mkSlice (w:=16) p10_B p9_B p9_L (by decide +kernel),by simp⟩
def p10_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[])]
def p10_t : Tabs := (p10_C.map (mkCut true p10_Z),[(3,2),(9,8),(37,36),(19,18),(6,4),(3,1),(42,40),(19,17),(12,8),(6,2),(20,16),(44,40),(24,16),(9,1),(44,36),(20,4),(52,36)],[],[[]])
theorem p10_W : TabsP true p10_R p10_T p10_t := ⟨cutsGood p10_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p10_D8 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw83],[0,1,4,17,8,33,12,5,9,25,49,16,20,13,21,29,37,41,45,53,57,61,65],[131,259,131,8195,259,16396,524,32780,524,65584,131120,262192,525376,1049664,6297600])]
def p10_D7 : List StD := []
theorem p10_I7 : LevelN true p10_T 7 p10_D7 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p10_C8x0 : levelOK true p10_T p10_t 7 (p10_D7.map Prod.fst) ((p10_D8.drop (0*32)).take 32) = true := by decide +kernel
theorem p10_I8 : LevelN true p10_T 8 p10_D8 := levelStep p10_B p10_W p10_I7 (chunks 32 p10_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p10_C8x0
  ))
theorem p10_L : LowN true p10_R p10_T 9 := lowSearch p10_B p10_I8 (by decide +kernel)
def p11_T : Nat := 0xfeeafcc0feeafcc0feeafcc0feeafcc0feeafcc0feeafcc0feeafcc0feeafcc0
def p11_R : List Nat := [0, 1, 2, 3, 4]
def p11_E : List (Nat × Nat × Nat) := [(0,16,17),(1,4,6),(2,2,6),(3,2,10),(4,1,17)]
theorem p11_B : baseOK p11_T p11_R p11_E = true := by decide +kernel
def p11_Z : List SliceD := [(pw0,5,[4, 2, 3, 1])]
theorem p11_Y : ∀ s ∈ p11_Z, SliceN true p11_R p11_T s := by
  unfold p11_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=1) p11_B p6_B p6_L (by decide +kernel),by simp⟩
def p11_C : List (Nat × List Nat) := [(0,[])]
def p11_t : Tabs := (p11_C.map (mkCut true p11_Z),[(17,16),(6,4),(19,18),(7,5),(6,2),(21,20),(7,3),(10,2),(25,24),(11,3)],[],[[]])
theorem p11_W : TabsP true p11_R p11_T p11_t := ⟨cutsGood p11_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p11_D5 : List StD := [
([pw0,pw1,pw2,pw4,pw10],[0,1,5,17,29,9,13,21,25,33,37],[102,394,1554,1,1,5,5,25,9,17])]
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
def p12_T : Nat := 0xfffefeeefff8f8a8fffefeeefff8f8a8fffefeeefff8f8a8fffefeeefff8f8a8
def p12_R : List Nat := [0, 1, 2, 3, 4, 5]
def p12_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,4,12),(4,4,20),(5,1,33)]
theorem p12_B : baseOK p12_T p12_R p12_E = true := by decide +kernel
def p12_Z : List SliceD := [(pw5,7,[0, 2, 3, 4, 5]),(pw3,7,[2, 0, 1, 5, 4]),(pw7,7,[2, 0, 1, 5, 3]),(pw91,7,[0, 2, 3, 4, 1]),(pw84,6,[1, 2, 3, 4, 5]),(pw92,5,[5, 3, 4, 2]),(pw93,5,[0, 2, 3, 4]),(pw6,6,[3, 1, 0, 5, 4]),(pw94,4,[2, 3, 4]),(pw4,6,[2, 4, 0, 1, 5]),(pw10,6,[2, 3, 0, 1, 5]),(pw83,6,[0, 1, 2, 3, 4]),(pw95,5,[4, 1, 0, 5]),(pw96,5,[3, 1, 0, 5]),(pw97,5,[1, 2, 3, 4]),(pw98,5,[2, 1, 0, 5]),(pw99,4,[0, 1, 5])]
theorem p12_Y : ∀ s ∈ p12_Z, SliceN true p12_R p12_T s := by
  unfold p12_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p12_B p7_B p7_L (by decide +kernel),mkSlice (w:=0) p12_B p7_B p7_L (by decide +kernel),mkSlice (w:=0) p12_B p7_B p7_L (by decide +kernel),mkSlice (w:=0) p12_B p7_B p7_L (by decide +kernel),mkSlice (w:=0) p12_B p11_B p11_L (by decide +kernel),mkSlice (w:=2) p12_B p6_B p6_L (by decide +kernel),mkSlice (w:=2) p12_B p6_B p6_L (by decide +kernel),mkSlice (w:=0) p12_B p11_B p11_L (by decide +kernel),mkSlice (w:=0) p12_B p1_B p1_L (by decide +kernel),mkSlice (w:=8) p12_B p9_B p9_L (by decide +kernel),mkSlice (w:=16) p12_B p9_B p9_L (by decide +kernel),mkSlice (w:=32) p12_B p9_B p9_L (by decide +kernel),mkSlice (w:=8) p12_B p6_B p6_L (by decide +kernel),mkSlice (w:=16) p12_B p6_B p6_L (by decide +kernel),mkSlice (w:=32) p12_B p6_B p6_L (by decide +kernel),mkSlice (w:=8) p12_B p6_B p6_L (by decide +kernel),mkSlice (w:=0) p12_B p1_B p1_L (by decide +kernel),by simp⟩
def p12_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(1,[261]),(2,[261]),(9,[]),(10,[]),(1,[262]),(2,[262]),(11,[]),(0,[128]),(1,[128]),(12,[]),(3,[128]),(0,[129]),(1,[129]),(13,[]),(2,[129]),(14,[]),(0,[130]),(1,[131]),(0,[257]),(15,[]),(0,[258]),(0,[385]),(1,[517]),(0,[513]),(1,[389]),(2,[389]),(1,[390]),(2,[390]),(1,[257]),(1,[393]),(2,[393]),(0,[261]),(16,[]),(3,[261]),(0,[262]),(3,[262]),(0,[389]),(1,[513]),(3,[389]),(0,[390]),(3,[390]),(0,[517]),(0,[393]),(3,[393]),(0,[521]),(0,[525]),(0,[514]),(3,[513]),(1,[261,406]),(2,[261,406]),(0,[128,277]),(0,[128,405]),(0,[128,533]),(0,[258,405]),(0,[386,277]),(1,[389,278]),(2,[389,278]),(0,[261,406]),(3,[261,406]),(0,[389,278]),(3,[389,278])]
def p12_t : Tabs := (p12_C.map (mkCut true p12_Z),[(34,32),(3,2),(3,1),(12,8),(5,4),(5,1),(12,4),(11,10),(25,17),(20,4),(19,18),(25,9),(34,2),(33,32),(33,1),(38,36),(14,10),(11,9),(14,6),(19,17),(22,6),(20,16),(44,40),(38,6),(44,36),(41,9),(52,36),(49,17),(7,6),(24,16),(24,8),(3,6),(37,36),(3,9),(3,17),(13,9),(21,17),(33,9),(33,17),(5,0),(3,10),(41,40),(24,9),(19,1),(5,17),(3,18),(49,48),(12,10),(34,6),(24,17),(19,2),(5,9),(20,0),(5,36),(33,0),(42,10),(50,18),(22,18),(7,1),(42,40),(26,18),(50,48),(26,10),(56,48),(52,48),(34,36),(37,1),(3,0),(56,40),(34,0),(38,4),(5,6),(12,36),(11,2),(11,1),(12,0),(20,36),(7,2),(24,40),(12,6),(20,6),(24,18),(20,18),(24,10),(33,16),(33,8),(7,4),(11,8),(19,16),(34,18),(34,10),(25,1),(13,1),(14,2),(44,32),(24,0),(24,32),(22,4),(14,4),(12,2),(3,16),(19,0),(3,8),(11,0),(34,4)],[],[[]])
theorem p12_W : TabsP true p12_R p12_T p12_t := ⟨cutsGood p12_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p12_D9 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw83],[3,0,4,8,12,1,25,33,37,45,49,5,9,13,17,21,29,41,53,57,61,65,69,73,77,81,85,89,93,97,101,105,109],[6179,59393,65733,131849,787473,3145763,12582951,50331691,5171,8389,67109641,402654225,717,1610612821,6442451225])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p12_D8 : List StD := [
([pw0,pw1,pw11,pw2,pw4,pw10,pw83],[20,0,16,24,5,57,3,32,36,40,13,25,117,121,12,28,29,37,41,85,93,101,109,113],[22,2,8388629,65557,262165,61,6,3,3,3,3,33921,129,129,16457,7488,664128,1048616,15168,2097192,4194344]),
([pw12,pw0,pw1,pw2,pw4,pw10,pw83],[16,24,0,57,3,33,45,113,52,56,25,4,8,28,44,48,5,9,13,21,29,37,41,49,85,93,101,109],[4,131077,532497,18465,36929,11,7,65665,1048705,4194433,11,6,6,6,8388614,263472,18874960,33554442,1904,67108874,134217738]),
([pw100,pw0,pw1,pw2,pw4,pw10,pw83],[28,16,5,65,3,20,64,9,24,68,72,25,53,85,0,4,8,12,32,44,48,60,76,1,13,17,21,29,41,57,69,77,89,97,109,117,125],[33554435,16657,67108865,557073,1114129,2228497,4102,68719476739,134217734,268435462,4102,16777225,1073742048,2147483872,8388832,8201,8201,4294967305,34359741952,8589938176,17721196544]),
([pw0,pw1,pw2,pw13,pw4,pw10,pw83],[20,72,80,1,28,88,33,57,113,84,96,21,45,32,92,9,25,37,49,61,93,117,121,125,129,133,137,141,145,149,153],[33037,8390929,16,66371,151841,16785793,524301,32781,33554511,67113005,32781,1,134285330,268568624,1059984,2097730,4214816,271488,66114,536872642,1073763488]),
([pw14,pw0,pw1,pw2,pw4,pw10,pw83],[32,28,72,100,1,88,49,9,17,33,13,25,45,57,85,4,8,104,21,37,61,93,133,137,149,153,157,3],[2,153,134479873,33285,69665,8257,153,67109123,773,4385,8257,1048603,4194333,8388665,153,19462,541730,2097219,133636,16777285,33554529]),
([pw101,pw0,pw1,pw2,pw4,pw10,pw83],[72,20,61,117,88,96,37,32,93,25,5,9,53,57,0,17,21,33,45,157,3],[1081345,16391,3,521,81,417,7174,589827,131083,262226,13346,135,15,86,10374,521,81,417,521,297,368]),
([pw0,pw1,pw2,pw4,pw15,pw10,pw83],[72,32,108,1,112,21,4,29,37,45,49,20,96,9,13,33,57,65,85,89,137,153,161,165],[8334,16547,4227075,65,914,8455298,131117,77,2061,1051164,9230,16417,262177,273,524323,2,65,32835,273,5123,2101778]),
([pw16,pw0,pw1,pw2,pw4,pw10,pw83],[72,20,4,96,112,116,69,21,57,8,88,9,33,37,169,173,177,3],[4,2147,131,4101,132609,265,106,131,5,16402,266,227,5,32882,106,21,65553,137,5,5,8472]),
([pw0,pw1,pw2,pw4,pw10,pw17,pw83],[88,20,120,1,21,96,112,124,41,45,9,13,25,33,57,32,49,133,149,177,181,185,189,193],[1294,2323,12738,1049091,65,2113826,4194335,139342,15,1038,1038,2065,524817,2065,8388657,4737,4289,286944,2,16929,98337]),
([pw18,pw0,pw1,pw2,pw4,pw10,pw83],[96,88,32,9,112,21,37,41,57,4,5,45,49,121,133,189,197,201,205,209,3],[1025,13,35,1049105,2051,259,13,35,65681,131075,4481,32774,16412,14,13,262194,524386,5,8258,5,5]),
([pw0,pw1,pw2,pw4,pw10,pw83,pw102],[32,96,128,1,129,3,132,136,9,25,117,121,0,5,13,37,49,53,57,61,69,77,85,165,185,213],[269,131089,8388625,16777233,33816593,8193,524301,1048589,2097165,269,4141,18016,4229280,3,3,3808,3,3,3,3,65537]),
([pw103,pw0,pw1,pw2,pw4,pw10,pw83],[32,1,49,129,3,9,33,45,88,112,140,144,25,4,5,13,21,37,53,57,61,69,77,85,93,165,185,217,221,225],[16385,35,65809,8769,897,524289,35,262153,33554441,67108873,134217741,1048579,2097155,4194307,35,37968,8521872,16777221,7376,268435461,536870917]),
([pw0,pw1,pw2,pw19,pw4,pw10,pw83],[20,0,72,5,24,148,117,88,65,93,25,53,57,8,9,17,29,37,41,121,149,153,229],[11,32777,2057,65545,262153,2057,3,16387,3,3,3,2,1380,4325764,4884,101,532609,4113,1124,1049204,2097808]),
([pw104,pw0,pw1,pw2,pw4,pw10,pw83],[32,88,20,72,24,5,25,37,57,17,12,61,193,233,3],[551,2054,1,74,134,17427,549,551,45,39,309,8199,77,135,277,74,138,4115,74,345,403]),
([pw0,pw1,pw2,pw4,pw20,pw10,pw83],[20,32,0,72,5,21,24,57,17,69,73,237,8,88,9,13,29,37,41,53,85,89,109,241],[2564,275,65555,275,262163,524307,5,5,16389,5,2564,32808,41,1048616,2097194,4,8389640,1226,143361,195,4194498]),
([pw0,pw1,pw2,pw4,pw10,pw105,pw83],[88,32,20,0,21,5,24,57,77,81,245,4,72,9,13,17,25,29,53,85,89,101,157,249],[1288,4194355,131110,39,32775,262182,13,12,13,8201,1288,16401,524305,21,1048595,8389121,71681,2097346,8,707,195]),
([pw0,pw1,pw2,pw4,pw10,pw83,pw106],[32,0,5,49,24,61,3,152,156,17,25,117,121,1,9,13,29,37,41,53,85,93,221,225,237,245],[7,517,65541,262149,524293,517,8226,16777250,33554466,11,16387,36032,1184064,2097161,17,7616,4194313,17,8388617,17,2]),
([pw0,pw1,pw2,pw4,pw88,pw10,pw83],[72,164,88,4,160,1,13,3,25,45,32,168,5,9,37,49,8,53,57,65,81,89,105,141],[12464,8388677,265,5123,16898,428160,524401,57,51,1049142,43184,77,9,16455,2097221,4,269,265,65667,1027,4194818]),
([pw107,pw0,pw1,pw2,pw4,pw10,pw83],[88,4,121,172,61,3,32,33,93,141,176,9,37,24,96,5,13,17,21,25,45,53,57,65,81,89,105,117,241,253],[131169,8273,262145,524291,4101,16705,34872,66049,134217858,1048581,6292768,8388633,268435594,16777221,3384,515,4101,33554945,7,536871042,67108869]),
([pw0,pw1,pw2,pw4,pw10,pw21,pw83],[88,72,180,1,8,184,25,164,145,3,32,188,5,9,37,49,4,33,53,57,73,85,97,229,257],[12812,2097409,131170,16401,5249,821760,8388877,1048686,29,141,43532,193,273,17,16777473,99,66083,4194402,3,16401,1153]),
([pw108,pw0,pw1,pw2,pw4,pw10,pw83],[88,164,25,61,3,32,192,93,145,196,9,24,96,5,17,21,33,37,53,57,73,85,97,121,209,229,257],[16433,2089,32769,7,131073,4257,9304,2097409,65542,3,787088,33554505,1048582,3,1752,7,25166081,67109121,7,4194310,3]),
([pw0,pw1,pw2,pw4,pw10,pw83,pw109],[96,32,164,200,5,1,24,93,9,117,121,12,17,25,37,89,257,72,88,29,41,53,61,69,77,193],[314,4115,524307,1048595,2097171,4115,4194408,8388712,16777320,427,329,107012,115716,33554567,2,26116,2179,131589,2179,263173,5]),
([pw110,pw0,pw1,pw2,pw4,pw10,pw83],[88,96,164,24,17,25,37,57,89,0,9,49,93,121,133,161,217,261,265,3],[19,524809,9,37,67,4099,1050,19,32774,19,65682,131337,16428,5,2178,37,8513,262147,37,38,7]),
([pw0,pw1,pw2,pw4,pw10,pw22,pw83],[88,164,204,1,21,13,33,3,4,208,9,49,5,25,53,57,65,85,89,117,121,241,253],[5260,49,524354,3,3,51840,65565,2097230,15,15,3724,49,131089,49,262161,1048835,8195,4194370,257,3,3]),
([pw0,pw1,pw2,pw4,pw10,pw83,pw111],[164,24,96,212,1,17,13,12,9,37,21,29,97,121,221,253,72,88,5,41,53,61,69,77,85],[282,262245,2085,524325,1048614,2084,2097178,4194330,8388634,16670,282,37953,16785985,199,66565,45569,135,2,16519,131589,1]),
([pw0,pw1,pw2,pw4,pw10,pw83,pw112],[96,88,216,5,65,24,1,69,12,164,21,41,225,72,17,25,29,53,85,105,269,273],[1048653,16393,65545,2057,131081,2057,1110,228,102,4229,165,1042,262162,19,19,2621442,4353,41473,259,35,513])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p12_D7 : List StD := [
([pw113,pw0,pw1,pw2,pw4,pw10],[96,220,9,93,113,3,228,232,25,117,121,277,224,5,13,29,37,41,57,69,77,85,101,109,281],[4098,2054,262153,4194313,8388617,2054,8209,32785,131089,16777222,524294,1048582,17248,2163872,2016]),
([pw0,pw1,pw11,pw2,pw4,pw88,pw10,pw83],[57,5,9,81,25,65,164,13,49,69,93,113,121,3,40,72,168,1,17,21,29,37,73,117,137,153,173,181,201,205,285,289],[1073741830,262144,2050,1048578,2050,402653186,259,131072,164,516,516,83886084,261,160,4194320,32832,2097224,73729,536870960,524288,4136,1025,8388608,4120,2147483665,24584,1025,33554441]),
([pw107,pw0,pw1,pw11,pw2,pw4,pw10,pw83],[93,121,5,9,57,24,88,37,65,117,13,113,0,32,176,1,17,21,25,33,81,133,137,149,153,161,181,285,293,297,301,3],[2052,4136,8288,131072,262144,130,49,134217740,65536,2052,301989892,67108870,21,32768,1288,538968072,4194314,25,1344,524800,1048642,2147500033,1073742592,130,17,130,8389121,16777219]),
([pw0,pw1,pw11,pw2,pw4,pw10,pw21,pw83],[57,5,9,25,229,37,49,77,85,93,113,117,3,24,32,36,88,188,1,17,21,41,73,81,121,133,149,161,177,285,293,297,305],[536870918,524288,1026,1207959554,2097154,1026,67,262144,276,2181038084,132,132,69,272,4194312,8388640,90112,135169,2072,268435504,1048576,513,2056,36872,67108873,16777216,4294967329,513]),
([pw108,pw0,pw1,pw11,pw2,pw4,pw10,pw83],[93,117,5,9,57,24,88,25,121,229,85,113,0,32,196,1,17,21,37,45,73,133,137,149,153,161,173,181,201,209,285,3],[2052,4136,8288,131072,130,262144,49,1073741836,65536,2052,33554438,402653188,21,32768,1544,2097162,71303176,25,1600,1048578,524608,2147500033,130,536871680,17,130,8388611,16777473]),
([pw0,pw1,pw11,pw2,pw4,pw10,pw22,pw83],[21,57,5,9,65,121,36,29,49,69,101,24,32,88,208,1,13,17,25,33,41,45,77,85,117,193,285,309,313,3],[67108876,131072,134217733,132,1048580,132,262,32768,25,520,4194312,520,266,65537,17301504,2097184,14336,536887298,17,8388609,17,33554435,96,262144,1026,64,268435490,1026]),
([pw0,pw1,pw2,pw28,pw4,pw10,pw83],[32,1,17,57,5,25,37,49,117,121,21,61,4,8,72,88,29,41,93,101,109,141,145,237,245],[23,21,21,65541,131077,141,2051,2051,8388611,16777219,139,1,2098464,4195904,262153,20768,41536,137,864,524297,1048585]),
([pw12,pw0,pw1,pw2,pw4,pw88,pw10,pw83],[45,49,13,25,1,32,37,5,57,72,164,29,93,141,4,56,9,17,21,61,117,153,189,205,269,289,317,321,3],[131072,65536,8196,16904,1568,1089,258,16777360,8196,2184,2208,65,258,4194324,67108888,524336,134217745,258,8388620,262144,69,4102,1048576,73,33554442,268468225,4130,2097155]),
([pw107,pw12,pw0,pw1,pw2,pw4,pw10,pw83],[93,121,61,113,57,117,32,72,37,1,5,33,45,141,9,13,17,21,25,149,153,269,301,321,325,3],[33554624,1096,580,131072,262144,258,81,65536,16384,41088,2208,4098,17,2097164,1032,2088,4106,25,516,16777252,8388614,21,4202528,258,17,258,524321,1048579]),
([pw12,pw0,pw1,pw2,pw4,pw10,pw21,pw83],[25,49,85,1,37,32,33,5,57,88,41,93,145,8,52,164,9,17,21,61,121,149,177,269,305,317,321,329,3],[131072,65536,4100,65,8720,33312,258,8388744,4100,65,1168,1184,258,134217740,33554441,67108888,524328,258,69,4194324,262144,2054,65,268451841,2097155,1048576,16777234,2082]),
([pw108,pw12,pw0,pw1,pw2,pw4,pw10,pw83],[93,117,61,113,45,57,32,164,25,1,5,33,121,145,9,17,21,37,85,149,153,209,269,317,333,3],[33554624,1096,580,65536,258,131072,97,32768,16384,270464,2178,4240,33,4194316,1032,2058,4120,41,516,8388614,16777236,37,258,2105360,33,258,524291,1048593]),
([pw12,pw0,pw1,pw2,pw4,pw10,pw22,pw83],[13,49,1,117,32,21,121,57,56,5,33,45,101,72,164,9,17,29,37,85,189,193,237,269,313,325,333],[65536,32768,33,1032,2112,24592,130,8389124,33,1032,2112,131600,130,1048581,33554444,67108932,4194324,130,33,524289,33,2097155,264,256,4106,262144,16777282,4114]),
([pw0,pw114,pw2,pw4,pw10,pw83],[32,164,9,53,25,61,85,285,13,29,37,41,69,77,121,149,153,193,269,301],[262157,137,521,2057,137,37,4101,8197,37,524370,322,131075,17426,32771,65539]),
([pw0,pw1,pw2,pw115,pw10,pw83],[32,164,236,1,9,85,205,5,25,37,57,121,125,133,137,149,153,161,181,189,193,217],[29,4099,131075,262147,2098305,524303,8207,16399,29,98,98,1048579,2818,32771,65539]),
([pw0,pw1,pw2,pw4,pw116,pw83],[32,164,240,1,9,25,177,5,13,37,57,121,125,133,137,149,153,161,181,189,193,217,301],[29,4099,131075,262147,2098305,524303,8207,16399,29,4194402,322,1048579,2594,32771,65539]),
([pw0,pw1,pw2,pw4,pw10,pw117],[32,164,244,1,213,5,9,25,85,13,29,37,41,61,69,77,121,149,153,193,301],[77,49,1041,4113,49,8205,16397,32781,77,1048962,770,524291,67714,131075,262147]),
([pw0,pw1,pw2,pw13,pw4,pw10,pw83],[164,32,1,17,33,9,45,21,49,57,25,61,93,113,117,121,133,137,149,153,177,205],[8236,3,1,27,75,778,2055,38,65543,131079,38,2,2097297,1048769,4099,16401,32833,770,1041,262147,524291]),
([pw0,pw1,pw2,pw4,pw44,pw83],[32,72,248,1,9,21,57,25,181,13,29,49,117,189,193,293,301,337],[29,35,32771,1281,131393,8207,15,29,29,65698,546,16387,4226,67,2113]),
([pw0,pw1,pw2,pw50,pw10,pw83],[32,72,252,1,9,21,41,57,85,5,25,49,77,109,117,161,189,193,341],[29,35,515,32833,262337,65551,29,4109,29,290,290,131075,17410,2051,8321]),
([pw118,pw0,pw2,pw4,pw10,pw83],[32,9,269,57,3,256,260,25,61,117,121,13,17,37,53,69,77,85,101,109,281,345,349,353],[4103,259,32771,65539,259,2097157,4194309,8388613,16397,2736,140368,1048585,1776,262153,524297]),
([pw0,pw1,pw2,pw4,pw88,pw10,pw83,pw102],[9,45,53,141,37,57,1,13,25,69,101,165,3,32,72,136,160,164,5,21,49,89,97,117,137,153,189,205,213],[69,140,2052,2052,22,268435492,262144,67108873,513,513,16777219,65,69633,134217992,524288,26,2097160,136,8388608,18,1056,4194560,36866,1056,155648,33554466,18,1048576]),
([pw107,pw0,pw1,pw2,pw4,pw10,pw83,pw102],[9,121,53,33,57,61,13,37,32,96,45,89,117,129,172,5,21,25,49,133,137,149,153,213,301,3],[8196,33,65536,131072,130,784,768,37,8196,4108,1030,8388628,32768,33,524297,1048579,33,33570817,16777288,130,2128,2112,130,2097176,4104,4194322,1026,262144]),
([pw0,pw1,pw2,pw4,pw10,pw21,pw83,pw102],[9,33,53,145,25,57,1,37,77,85,109,185,3,32,96,132,180,5,21,49,105,121,133,149,177,213,257,329],[69,524,22,2052,2052,33554468,131072,134217737,4194307,257,257,65,69633,26,16777352,262144,67108872,520,18,36866,8388642,18,2097152,1056,1048704,1056,24576,524288]),
([pw108,pw0,pw1,pw2,pw4,pw10,pw83,pw102],[9,117,53,45,57,61,25,85,32,96,33,121,129,257,192,5,21,37,49,133,137,149,153,209,213,3],[4100,33,65536,66,131072,784,768,37,4100,1030,2060,16777236,32768,33,524291,1048585,33,33570817,66,8388744,8336,8320,66,2097170,1026,4194328,2056,262144]),
([pw0,pw1,pw2,pw4,pw10,pw22,pw83,pw102],[9,21,53,13,45,57,33,132,1,69,101,117,121,32,96,204,5,25,49,77,85,89,109,165,189,213,3],[261,14,2116,4116,8388612,33554468,65536,16777219,513,524289,513,257,67141633,10,1048578,10,2097154,10,144,131072,1120,2112,128,4194352,4112,1056,24576,262144]),
([pw0,pw1,pw2,pw119,pw4,pw10,pw83],[96,32,1,17,9,21,25,37,53,117,121,4,72,88,164,61,69,77,113,141,145,165,185],[262172,265,265,2097161,4194313,265,32806,22,65542,131078,22,1,524896,1049760,3,6720,25728,3,1728,3,3]),
([pw103,pw0,pw1,pw2,pw4,pw88,pw10,pw83],[1,45,13,25,49,37,9,165,72,164,53,69,93,141,4,144,5,21,57,117,137,189,205,217,289,357,3],[65536,65,8196,16648,768,546,262144,65,8196,1160,1152,34,8388752,2097157,2049,2049,1048579,65,4194316,131072,38,4116,524288,42,16777240,67141634,4112,33554450]),
([pw103,pw107,pw0,pw1,pw2,pw4,pw10,pw83],[1,45,33,37,49,141,164,96,9,13,61,93,117,129,5,21,25,53,57,133,137,217,301,357,361,3],[33554624,16384,257,608,4164,74,262144,139392,1025,32768,65536,10,2192,257,544,4100,10,2105360,1025,524293,1048579,257,4194340,42,2096,14,16777236,8388626]),
([pw103,pw0,pw1,pw2,pw4,pw10,pw21,pw83],[1,25,85,49,33,37,9,185,88,164,53,77,93,145,140,5,21,57,121,133,177,217,305,329,361,3],[32768,65,8196,18,800,768,131072,65,8196,18,1184,1152,2097288,8388613,524291,2049,2049,65,22,1048612,65536,4108,18,33570818,16777226,262144,4194344,4104]),
([pw103,pw108,pw0,pw1,pw2,pw4,pw10,pw83],[1,33,25,45,49,145,164,96,9,61,85,93,121,129,5,21,37,53,57,133,137,209,217,357,361,3],[33554624,16384,257,1120,70,4168,262144,139392,513,32768,6,65536,2192,257,1056,6,4104,4202512,513,524291,1048585,257,38,2097192,2096,6,16777234,8388632]),
([pw103,pw0,pw1,pw2,pw4,pw10,pw22,pw83],[1,13,49,21,121,9,117,140,33,45,53,69,221,88,164,5,25,57,77,85,165,189,193,217,313],[32768,33,10,320,528,24576,131072,33,10,320,528,1049600,8389636,2097155,2049,262145,2049,33,10,524290,10,4194310,144,65536,4164,128,16777236,4100]),
([pw0,pw1,pw2,pw4,pw10,pw120],[164,96,200,65,1,9,17,121,229,5,25,37,73,133,137,161,181],[52,67,32771,65539,578,13,8197,16389,52,265,265,15,3201,4099,131]),
([pw0,pw1,pw2,pw4,pw88,pw10,pw83,pw106],[17,81,13,25,49,5,160,1,37,65,73,93,121,72,96,156,164,9,21,29,53,61,117,181,201,205,221,357,3],[33,33,524289,33,25165825,1048577,33,516,1032,2097280,386,80,131072,33554444,262144,4102,2068,516,4194304,4106,67108888,1032,268468226,2064,90112,134217746,258,64]),
([pw107,pw0,pw1,pw2,pw4,pw10,pw83,pw106],[5,121,49,1,17,241,164,37,172,13,61,81,93,117,32,96,9,21,25,53,65,161,181,293,301,357,361],[17,1032,131072,262144,130,4100,49216,17,17,10485761,4194307,524289,17,1032,8232,2058,260,65536,16777760,130,4100,1049152,130,67108900,8288,33554438,2050,256]),
([pw0,pw1,pw2,pw4,pw10,pw21,pw83,pw106],[17,25,49,85,5,37,180,73,81,93,117,229,32,96,152,164,1,9,21,41,53,61,121,161,177,225,293,361,3],[17,17,75497473,524289,17,1048577,17,2056,130,288,2162688,68,131072,1034,16777256,262144,524,2056,1026,268451842,134217734,130,4194304,33554468,288,516,45056,64]),
([pw108,pw0,pw1,pw2,pw4,pw10,pw83,pw106],[5,117,49,1,17,249,25,192,61,73,85,93,121,32,96,9,21,37,53,161,181,201,209,229,357,361],[17,264,65536,66,131072,2052,24576,17,17,524291,3145729,262145,17,264,522,4136,132,32768,66,4195360,2052,8389632,66,33554438,514,16777252,4128,128]),
([pw0,pw1,pw2,pw4,pw10,pw22,pw83,pw106],[17,21,49,65,121,5,117,152,204,29,221,241,249,32,96,1,9,25,41,53,85,193,225,237],[33,33,513,262145,513,524289,33,10,2112,4112,8421376,260,65536,10,1048578,10,2097158,10,144,131072,1092,2112,128,4194324,4112,1028,24576,256]),
([pw121,pw0,pw1,pw2,pw4,pw83],[164,45,264,141,365,37,3,268,1,9,25,49,5,13,53,57,65,73,81,89,97,105],[35,262147,35,35,2097155,4932,8201,1041,51392,65549,131093,3012,1049,524297,1048593]),
([pw0,pw122,pw1,pw2,pw4,pw10,pw83],[164,21,45,33,1,9,13,37,49,57,24,17,117,0,96,65,81,89,105,113,121,129,241,253],[1,526384,67,4105,133,2099968,9264,67,4105,1048581,18176,32771,4194313,65541,816,67,135,131075,141,8388617,262149]),
([pw123,pw0,pw1,pw2,pw10,pw83],[164,33,272,365,369,25,3,276,1,9,37,49,5,53,57,73,81,97,105,301,373,377],[35,32771,35,35,131075,4932,524305,1033,26816,1048597,65549,3012,1049,2097169,262153]),
([pw0,pw124,pw1,pw2,pw4,pw10,pw83],[164,21,33,45,1,9,25,49,57,85,24,17,121,0,96,73,97,113,117,129,229,249,257,273],[1,133168,515,69,4105,526720,9264,515,262149,4105,17792,1048579,32773,2097161,432,71,515,4194307,69,65541,8388617]),
([pw0,pw125,pw2,pw4,pw10,pw83],[96,164,5,25,189,37,117,53,121,17,29,41,49,57,89],[133,517,1029,2053,133,16402,74,290,12289,90,306,19,74,11,35])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p12_D6 : List StD := [
([pw113,pw0,pw1,pw2,pw4,pw88,pw10],[81,217,9,57,141,73,5,13,25,29,37,121,232,21,65,69,93,117,181,205,277,3],[66,1048588,152,296,65544,1033,66,146,514,514,262147,16404,292,32772,1029,524336,8192,2065,131072,2081,2101249]),
([pw113,pw107,pw0,pw1,pw2,pw4,pw10],[57,81,33,5,9,93,121,281,37,113,117,13,21,25,133,181,301],[33,33,33,33,1029,259,520,144,4096,8192,66,152,520,1028,32778,144,16404,258,67588,66,70]),
([pw113,pw0,pw1,pw2,pw4,pw10,pw21],[73,217,9,57,145,81,5,25,37,41,85,117,228,21,77,93,121,161,177,229,277,3],[66,1048588,1048,137,296,32776,66,1042,131075,514,514,524308,133,292,16388,2065,262192,8192,2049,2101249,65536]),
([pw113,pw108,pw0,pw1,pw2,pw4,pw10],[57,73,45,5,9,93,117,281,25,113,121,21,37,85,137,161,209],[33,33,33,33,259,1029,520,144,2048,66,4096,152,520,32778,1028,144,258,16404,66,73732,70]),
([pw113,pw0,pw1,pw2,pw4,pw10,pw22],[21,217,9,57,13,45,228,5,33,69,117,121,25,29,65,77,85,101,277],[130,262156,25,1288,2088,131080,130,19,1282,2082,8194,16389,516,32772,516,17,65537,17,96,4096,64]),
([pw121,pw0,pw1,pw11,pw2,pw4,pw83],[93,5,9,209,25,37,57,65,69,113,381,268,1,17,21,29,73,81,285,385,3],[514,260,131104,16424,1072,97,262150,8192,514,32770,67,4096,140,260,69,136,65552,1050625,1048,73,524305]),
([pw123,pw0,pw1,pw11,pw2,pw10,pw83],[93,5,9,73,301,37,57,25,113,373,381,276,1,17,21,41,77,81,285,385,3],[258,140,136,16408,1064,73,262150,8192,258,32770,67,4096,532,65540,69,528,131104,1050625,1072,81,524321]),
([pw121,pw12,pw0,pw1,pw2,pw4,pw83],[37,93,25,57,13,45,1,365,141,5,9,17,189,269,317,321,385,389],[33,33,163841,33,33,11,2048,1024,272,132,10,8768,272,132,10,4176,16452,10,148,10,65542]),
([pw126,pw0,pw1,pw2,pw4,pw10,pw83],[5,49,121,1,117,13,17,37,57,21,33,61,9,25,93,149,153,181,321,325],[65,6152,544,9232,132,258,65,65,1041,131077,259,2056,524312,262156,266,544,164,16418,148,32786,65542]),
([pw123,pw12,pw0,pw1,pw2,pw10,pw83],[25,93,37,57,33,301,1,365,369,5,9,17,269,317,321,385,393,397],[17,17,73729,17,17,11,2048,1024,288,132,10,4672,288,132,10,131168,16452,10,164,10,32774]),
([pw127,pw0,pw1,pw2,pw4,pw10,pw83],[5,49,117,1,85,121,17,25,57,21,45,61,9,37,93,149,153,161,317,333],[65,6152,528,132,9248,258,65,65,131077,1057,259,2056,262156,524328,266,148,528,16402,132,32774,65570]),
([pw118,pw0,pw2,pw4,pw88,pw10,pw83],[9,57,269,141,37,13,25,69,121,277,281,349,260,17,21,101,117,137,153,173,205,401,405,3],[8197,41,129,129,655361,515,44,2052,2052,6291460,518,1048648,16384,280,1034,65536,336,32770,8392720,1026,262162]),
([pw107,pw118,pw0,pw2,pw4,pw10,pw83],[9,121,57,269,61,37,281,117,345,13,21,25,133,149,153,173,297,301,401,409,413],[17,264,1024,2048,34,68,17,17,69633,32771,17,264,1572872,262154,76,131712,34,68,34,8324,16390]),
([pw118,pw0,pw2,pw4,pw10,pw21,pw83],[9,57,269,145,25,77,85,117,277,281,353,256,17,21,37,109,121,133,149,177,297,409,413,3],[4101,73,1179649,33,33,259,76,6291460,1028,1028,262,152,540680,8192,522,144,8390672,262162,65536,32770,514]),
([pw108,pw118,pw0,pw2,pw4,pw10,pw83],[9,117,57,269,61,25,281,121,345,21,37,85,137,149,153,173,209,297,401,405,409],[17,264,512,34,1024,68,17,17,131075,36865,17,264,1048586,786440,76,34,67712,68,34,8198,16516]),
([pw118,pw0,pw2,pw4,pw10,pw22,pw83],[9,21,57,269,13,256,69,101,277,349,17,25,77,85,109,121,353,417],[1033,19,65,4097,65,261,26,520,65544,520,268,18,8194,18,131078,32800,2048,132,32,16388,132]),
([pw121,pw0,pw1,pw2,pw4,pw83,pw102],[37,69,141,45,53,101,25,365,1,9,13,57,264,5,49,89,189,213,3],[9,515,9,9,2081,9,274,1044,208,131120,8192,65542,514,258,266242,196,32804,1028,2080,192,16384]),
([pw123,pw0,pw1,pw2,pw10,pw83,pw102],[9,25,369,33,53,365,37,1,57,301,272,5,49,77,97,109,213,377,393,397,3],[10,262147,10,10,16386,10,145,532,112,65808,2048,524293,8193,129,1049601,100,131076,516,33056,96,4096]),
([pw103,pw121,pw0,pw1,pw2,pw4,pw83],[1,37,13,25,45,93,9,365,49,69,141,5,53,57,189,217,385],[18,2048,65,1028,136,8192,18,515,18,18,290,65,1028,136,36896,16389,513,65,140,292,65576]),
([pw128,pw0,pw1,pw2,pw4,pw10,pw83],[1,53,121,13,117,49,9,17,37,21,33,93,25,45,57,133,137,189,357,361],[130,65,520,5136,260,18464,67,130,1042,8198,130,131081,32785,65541,65,520,268,2088,276,524336,262180]),
([pw103,pw123,pw0,pw1,pw2,pw10,pw83],[1,25,301,33,37,93,9,365,49,369,5,53,57,77,217,385,393,397],[10,1024,65,516,144,4096,10,65539,10,10,290,65,516,144,18464,131077,8193,65,148,292,32816]),
([pw129,pw0,pw1,pw2,pw4,pw10,pw83],[1,53,117,85,49,121,9,17,25,21,45,93,33,37,57,133,137,329,357,361],[130,65,520,260,9248,18448,67,130,4102,1058,130,131081,32773,65569,65,268,520,2072,260,524308,262192]),
([pw121,pw0,pw1,pw2,pw4,pw83,pw106],[5,25,37,209,17,93,264,49,65,73,81,381,9,21,29,53,221],[17,1028,8204,2054,164,1028,17,17,16385,32769,17,264,514,96,4096,2058,168,264,65570,514,64]),
([pw123,pw0,pw1,pw2,pw10,pw83,pw106],[5,25,37,301,17,93,272,49,73,81,373,381,9,21,41,53,225],[17,258,8202,2054,162,258,17,17,16385,32769,17,1032,516,96,4096,2060,168,1032,65572,516,64])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p12_D5 : List StD := [
([pw113,pw121,pw0,pw1,pw2,pw4],[37,141,217,9,57,73,5,13,25,81,209,29,65,113,277,381],[513,68,16408,146,304,8197,513,1027,32801,68,134,2052,4106,296,1026]),
([pw113,pw123,pw0,pw1,pw2,pw10],[25,217,369,81,9,57,5,37,73,301,381,21,41,113,277,373],[257,66,16432,548,168,8195,257,2053,1033,66,518,4098,32788,152,1036]),
([pw121,pw118,pw0,pw2,pw4,pw83],[9,269,281,57,209,13,25,37,69,345,17,101,141,349,381],[257,514,48,16576,140,1027,4113,257,13,514,8194,14,48,28,2116]),
([pw123,pw118,pw0,pw2,pw10,pw83],[9,269,281,57,301,25,37,77,345,381,17,21,109,353,369],[129,258,2096,608,44,1027,16401,129,13,258,8194,14,592,28,4164])]
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p12_C7x1 : levelOK true p12_T p12_t 6 (p12_D6.map Prod.fst) ((p12_D7.drop (1*32)).take 32) = true := by decide +kernel
theorem p12_I7 : LevelN true p12_T 7 p12_D7 := levelStep p12_B p12_W p12_I6 (chunks 32 p12_D7 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p12_C7x0
  · exact p12_C7x1
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p12_C8x0 : levelOK true p12_T p12_t 7 (p12_D7.map Prod.fst) ((p12_D8.drop (0*32)).take 32) = true := by decide +kernel
theorem p12_I8 : LevelN true p12_T 8 p12_D8 := levelStep p12_B p12_W p12_I7 (chunks 32 p12_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p12_C8x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p12_C9x0 : levelOK true p12_T p12_t 8 (p12_D8.map Prod.fst) ((p12_D9.drop (0*32)).take 32) = true := by decide +kernel
theorem p12_I9 : LevelN true p12_T 9 p12_D9 := levelStep p12_B p12_W p12_I8 (chunks 32 p12_D9 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p12_C9x0
  ))
theorem p12_L : LowN true p12_R p12_T 10 := lowSearch p12_B p12_I9 (by decide +kernel)
def p13_T : Nat := 0xeeeaece8eeeaece8eeeaece8eeeaece8eeeaece8eeeaece8eeeaece8eeeaece8
def p13_R : List Nat := [0, 1, 2, 3, 4]
def p13_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,2,10),(4,1,17)]
theorem p13_B : baseOK p13_T p13_R p13_E = true := by decide +kernel
def p13_Z : List SliceD := [(pw3,5,[0, 1, 2, 4])]
theorem p13_Y : ∀ s ∈ p13_Z, SliceN true p13_R p13_T s := by
  unfold p13_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p13_B p2_B p2_L (by decide +kernel),by simp⟩
def p13_C : List (Nat × List Nat) := [(0,[])]
def p13_t : Tabs := (p13_C.map (mkCut true p13_Z),[(5,4),(6,4),(3,2),(3,1),(6,2),(5,1),(10,2),(13,12)],[],[[]])
theorem p13_W : TabsP true p13_R p13_T p13_t := ⟨cutsGood p13_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p13_D5 : List StD := [
([pw0,pw1,pw2,pw4,pw10],[0,1,5,17,25,9,13,21,29],[102,170,275,3,204,5,5,25,9,17])]
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
def p14_T : Nat := 0xfeeefac0feeefac0feeefac0feeefac0feeefac0feeefac0feeefac0feeefac0
def p14_R : List Nat := [0, 1, 2, 3, 4]
def p14_E : List (Nat × Nat × Nat) := [(0,8,9),(1,4,6),(2,2,6),(3,1,9),(4,1,17)]
theorem p14_B : baseOK p14_T p14_R p14_E = true := by decide +kernel
def p14_Z : List SliceD := [(pw84,4,[1, 2, 3, 4]),(pw5,4,[0, 3, 2, 4]),(pw6,4,[0, 4, 1, 3]),(pw3,4,[1, 4, 0, 2]),(pw7,4,[2, 3, 0, 1])]
theorem p14_Y : ∀ s ∈ p14_Z, SliceN true p14_R p14_T s := by
  unfold p14_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p14_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p14_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p14_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p14_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p14_B p5_B p5_L (by decide +kernel),by simp⟩
def p14_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[])]
def p14_t : Tabs := (p14_C.map (mkCut true p14_Z),[(9,8),(11,10),(7,5),(21,20),(7,3),(9,1),(17,1),(12,8),(26,24),(11,3),(18,2),(12,4),(28,24),(21,5),(28,20),(26,10),(6,5),(6,3),(6,2),(6,4),(9,3),(17,5),(18,10),(7,4),(18,16),(12,5),(17,16),(18,3),(17,3),(7,2),(9,0),(17,0),(12,10),(9,10),(11,8),(14,8),(9,5),(12,20),(17,20),(21,16),(18,24),(26,16),(12,24),(12,0),(7,1),(12,16),(6,0),(6,1),(7,0),(11,2),(18,0),(18,8),(9,2),(17,2),(17,4)],[],[[]])
theorem p14_W : TabsP true p14_R p14_T p14_t := ⟨cutsGood p14_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p14_D6 : List StD := [
([pw0,pw1,pw2,pw4,pw10],[3,0,4,8,12,16,1,9,17,13,21,29,33,5,25,37,41,45,49,53,57,61],[8391,843,1619,16995,2445,37013,69797,133401,786729,3146801])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p14_D5 : List StD := [
([pw0,pw1,pw11,pw2,pw4,pw10],[25,45,73,5,9,21,29,41,16,1,65,69,77,81,85,89,3],[1048,512,2060,42,137,4096,84,8210,145,68,34,65793,38,16389,32771]),
([pw0,pw1,pw2,pw13,pw4,pw10],[21,41,77,13,17,25,45,97,12,1,65,69,73,81,85,89,93,3],[66564,2072,512,73,42,132,132,8197,38,4096,81,16402,131329,34,32771]),
([pw0,pw1,pw2,pw4,pw15,pw10],[25,73,77,21,41,1,9,17,29,45,61,81,85,101,105],[68,130,8232,16384,49,262,2060,68,21,258,130,4099,512,1033,17]),
([pw0,pw1,pw2,pw4,pw10,pw17],[45,73,77,21,25,9,17,1,29,41,57,81,85,105,109,113],[36,66,9,24592,128,262,2053,32788,36,11,4114,66,1025,9,512]),
([pw0,pw1,pw2,pw19,pw4,pw10],[25,45,73,77,1,37,41,5,21,29,53,65,69,89,93,97,117,121,125,129],[18440,69636,144,131090,262161,524300,32768,42,73,512,38,1029,258,65,8195]),
([pw0,pw1,pw2,pw4,pw20,pw10],[1,73,25,105,29,33,37,41,8,21,69,77,81,85,89,133,137,3],[98305,1027,9,9,9,18,4192,2048,164,18,131330,8198,512,16452,132]),
([pw0,pw1,pw2,pw4,pw10,pw105],[1,45,73,29,5,37,41,25,49,69,77,89,97,105,113,121],[17,517,32771,8193,17,12,34,20544,1024,14,260,12,2114,34,128]),
([pw0,pw1,pw2,pw4,pw88,pw10],[77,1,13,29,53,25,33,45,21,65,73,93,97,105,141,145,149],[2561,6,6,8194,6,16393,65,4097,65,32904,1024,56,256,65680,48]),
([pw0,pw1,pw2,pw4,pw10,pw21],[45,77,1,21,53,97,105,4,25,49,65,73,81,85,93,121,149,153,157,3],[17410,393220,32773,68,68,34,4099,34,524418,9,8720,2048,65553,9,256]),
([pw0,pw1,pw2,pw4,pw10,pw22],[73,77,29,105,1,61,97,0,21,25,57,65,69,89,93,117,161,165,169,3],[18434,36865,24,24,524424,7,196610,66,66,5,262177,5,9248,256,512])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p14_D4 : List StD := [
([pw27,pw0,pw1,pw2,pw4],[73,125,5,9,25,29,21,45,69,77,81],[6,536,49,208,6,259,6,41,1096,33]),
([pw33,pw0,pw1,pw2,pw10],[21,25,77,121,41,173,45,65,69,81,177,181],[73,517,65,19,140,296,26,1060,22,2082]),
([pw90,pw0,pw1,pw4,pw10],[41,73,185,25,173,29,1,69,81,117,181,189,193,197],[642,38,34,11,6148,8272,9,276,13,1041]),
([pw130,pw0,pw2,pw4,pw10],[45,77,185,21,201,1,29,65,85,93,97,105,189,193,205],[642,70,11,1026,12292,9,2080,13,276,16401]),
([pw58,pw1,pw2,pw4,pw10],[1,29,77,73,121,125,45,89,105,137,209,213,217],[517,11,81,257,14,1044,2084,10,4130,176])]
def p14_D3 : List StD := []
theorem p14_I3 : LevelN true p14_T 3 p14_D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p14_C4x0 : levelOK true p14_T p14_t 3 (p14_D3.map Prod.fst) ((p14_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p14_I4 : LevelN true p14_T 4 p14_D4 := levelStep p14_B p14_W p14_I3 (chunks 32 p14_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p14_C4x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p14_C5x0 : levelOK true p14_T p14_t 4 (p14_D4.map Prod.fst) ((p14_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p14_I5 : LevelN true p14_T 5 p14_D5 := levelStep p14_B p14_W p14_I4 (chunks 32 p14_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p14_C5x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p14_C6x0 : levelOK true p14_T p14_t 5 (p14_D5.map Prod.fst) ((p14_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p14_I6 : LevelN true p14_T 6 p14_D6 := levelStep p14_B p14_W p14_I5 (chunks 32 p14_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p14_C6x0
  ))
theorem p14_L : LowN true p14_R p14_T 7 := lowSearch p14_B p14_I6 (by decide +kernel)
def p15_T : Nat := 0xeeeaeee0eeeaeee0eeeaeee0eeeaeee0eeeaeee0eeeaeee0eeeaeee0eeeaeee0
def p15_R : List Nat := [0, 1, 2, 3, 4]
def p15_E : List (Nat × Nat × Nat) := [(0,4,5),(1,4,6),(2,1,5),(3,1,9),(4,1,17)]
theorem p15_B : baseOK p15_T p15_R p15_E = true := by decide +kernel
def p15_Z : List SliceD := [(pw6,4,[0, 3, 1, 4])]
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
([pw0,pw1,pw2,pw4,pw10],[1,9,13,0,21,29,5,17,25,33,37,41,45],[67,133,273,545,1030,2066,4130,12,12,24])]
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
def p16_T : Nat := 0xfefefeeefefafec0fefefeeefefafec0fefefeeefefafec0fefefeeefefafec0
def p16_R : List Nat := [0, 1, 2, 3, 4, 5]
def p16_E : List (Nat × Nat × Nat) := [(0,8,9),(1,4,6),(2,2,6),(3,1,9),(4,1,17),(5,1,33)]
theorem p16_B : baseOK p16_T p16_R p16_E = true := by decide +kernel
def p16_Z : List SliceD := [(pw84,6,[1, 2, 3, 4, 5]),(pw3,7,[0, 1, 2, 4, 5]),(pw85,5,[1, 2, 3, 5]),(pw131,5,[2, 1, 3, 4]),(pw132,5,[3, 1, 2, 0]),(pw5,5,[0, 2, 3, 4, 5]),(pw7,6,[1, 3, 0, 5, 2]),(pw6,5,[0, 1, 3, 5, 4]),(pw8,4,[0, 3, 2, 5]),(pw133,4,[0, 3, 1, 4]),(pw134,4,[0, 4, 2, 5])]
theorem p16_Y : ∀ s ∈ p16_Z, SliceN true p16_R p16_T s := by
  unfold p16_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p16_B p13_B p13_L (by decide +kernel),mkSlice (w:=0) p16_B p14_B p14_L (by decide +kernel),mkSlice (w:=0) p16_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p16_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p16_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p16_B p15_B p15_L (by decide +kernel),mkSlice (w:=0) p16_B p8_B p8_L (by decide +kernel),mkSlice (w:=0) p16_B p15_B p15_L (by decide +kernel),mkSlice (w:=0) p16_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p16_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p16_B p5_B p5_L (by decide +kernel),by simp⟩
def p16_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(1,[129]),(6,[257]),(7,[]),(1,[131]),(1,[257]),(1,[259]),(1,[260]),(8,[]),(9,[]),(1,[261]),(1,[262]),(1,[263]),(1,[389]),(1,[390]),(1,[517]),(1,[518]),(1,[393]),(1,[394]),(1,[521]),(1,[522]),(1,[260,21]),(4,[389]),(1,[258,149]),(1,[129,532]),(1,[129,534]),(1,[258,151]),(1,[131,405]),(1,[130,277]),(1,[257,404]),(1,[257,406]),(1,[130,279]),(1,[259,533]),(10,[]),(1,[260,405]),(1,[260,533]),(1,[392,149]),(1,[516,277]),(1,[390,21]),(1,[522,21])]
def p16_t : Tabs := (p16_C.map (mkCut true p16_Z),[(9,8),(19,18),(7,5),(37,36),(7,3),(9,1),(17,1),(33,1),(10,8),(12,8),(10,2),(26,24),(19,3),(34,32),(34,2),(12,4),(20,16),(20,4),(44,40),(37,5),(26,18),(44,36),(52,36),(50,18),(6,3),(6,2),(10,18),(12,36),(34,18),(6,4),(17,3),(33,5),(17,18),(17,16),(20,18),(38,36),(22,18),(6,0),(50,48),(6,18),(17,0),(20,36),(42,40),(28,24),(52,48),(33,36),(33,0),(6,1),(6,5),(9,3),(33,3),(9,2),(33,2),(34,0),(7,4),(7,2),(9,5),(37,4),(50,16),(10,24),(19,2),(34,48),(7,1),(9,4),(17,4),(10,0),(20,0),(17,5),(52,32),(12,40),(20,48),(19,16),(9,0),(34,36),(33,32),(6,36),(34,4),(12,0),(37,32),(12,1),(33,4),(6,8),(7,18),(10,1),(17,2),(10,16),(12,16),(12,32),(20,32),(7,36),(20,1)],[],[[]])
theorem p16_W : TabsP true p16_R p16_T p16_t := ⟨cutsGood p16_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p16_D8 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw83],[3,0,4,1,21,8,25,12,5,29,9,13,17,16,33,37,41,45,49,53,57,61,65,69,73,77,81,85,89,93],[1291,6155,286,362,2698,54273,65556,393313,1573505,2097172,12583009,50332289,67108884,134217748,805314656])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p16_D7 : List StD := [
([pw0,pw1,pw11,pw2,pw4,pw10,pw83],[0,12,20,24,8,9,25,28,21,29,3,5,37,61,69,101,32,41,49,57,77,97,105,109,113],[37,4,2100225,265,2241,515,1,37924,131372,262260,524838,103424,8456,16592,1538,8456,16592,1049090,4194328,8388618,16777426]),
([pw92,pw0,pw1,pw2,pw4,pw10,pw83],[20,8,12,36,101,1,41,57,3,24,9,13,25,32,61,69,77,105,109,113,117,121],[513,1048577,8465,585,259,133,1027,2082,42,4102,2086,1297,73,2097155,133,16472,36882,65684,131082,262156,524294]),
([pw0,pw1,pw2,pw13,pw4,pw10,pw83],[0,8,12,32,40,117,17,13,21,25,29,3,33,41,57,20,9,49,61,69,77,105,109,113],[67745,73,8,401,643,1157,6248,38944,8496,131618,17444,1,262488,524874,1049676,8464,2562,17412,2097170,4194324,8388614]),
([pw101,pw0,pw1,pw2,pw4,pw10,pw83],[32,8,12,44,117,69,1,61,3,40,5,17,29,20,41,49,57,101,105,109,113,125],[513,8465,131073,649,35,261,1090,2051,74,1122,4102,2321,16536,32818,69652,137,35,2097157,262154,524300,1048582]),
([pw0,pw135,pw1,pw2,pw4,pw10,pw83],[20,32,1,3,48,52,56,37,57,69,13,33,41,12,8,21,25,29,101,105,109,113,117,121,125,129,133,137],[8205,33556493,1166,37892,67174916,132356,4194305,262146,25,16425,8265,134217731,2065,8390689,321,146,674,16777410,528944,1053008,2098016]),
([pw0,pw1,pw2,pw19,pw4,pw10,pw83],[1,41,57,69,60,101,117,3,5,21,25,29,8,20,32,13,12,9,17,49,61,77,81,85,89,93,137,141,145],[131393,294945,4481,771,1289,34821,67133536,16384,594,524488,134219844,8192,1048626,268436520,2097316,530,5256,67716,4194330,8388630,50331660]),
([pw86,pw0,pw1,pw2,pw4,pw10,pw83],[20,52,64,1,41,49,9,57,3,12,5,13,37,69,32,60,21,29,33,61,73,77,85,89,105,117,141,149],[1801,262145,32769,21,35,897,33554505,6408,66580,8234,133256,134234177,21,35,67108929,524308,8226,3149952,16777222,4194324,8388642]),
([pw104,pw0,pw1,pw2,pw4,pw10,pw83],[32,56,68,52,61,69,77,13,3,5,17,33,57,12,60,21,25,37,41,45,49,81,93,101,109,145,149],[8577,16385,131073,21,297,67,2944,8389633,32916,66208,4162,67109897,262164,1574944,4170,21,33554473,67,2097172,16777222,4194410]),
([pw0,pw1,pw2,pw4,pw10,pw105,pw83],[8,52,1,45,5,37,72,101,3,16,13,21,29,49,153,56,25,41,57,61,73,77,85,105,113,157],[29,1029,21,21,21,1029,426,16394,11,1,16394,526496,33562881,33186,3149856,8388673,131138,4200512,65538,16785921,262658]),
([pw136,pw0,pw1,pw2,pw4,pw10,pw83],[8,20,16,76,101,25,41,57,3,1,13,45,56,49,61,69,77,81,109,129,161,165],[259,3,4370,74,8195,134,524291,1537,521,1048613,1029,2322,74,2051,134,16472,32801,65684,131081,262156,2097189]),
([pw0,pw1,pw2,pw4,pw10,pw83,pw106],[12,1,53,5,21,25,37,80,101,20,13,41,49,57,3,16,56,61,65,69,73,81,85,93,141,153,169],[15,1027,11,11,1027,11,16777540,67110932,33558564,517,1,131408,786528,1073153,82240,2097328,4194433,2192,8396801,36896,512]),
([pw93,pw0,pw1,pw2,pw4,pw10,pw83],[12,20,16,84,5,56,101,41,49,13,77,141,21,29,57,61,69,105,109,165,3],[19,3,1048674,138,262,16387,19,529,4105,21,529,2146,138,262,2051,33000,65892,9217,131084,262153,525317]),
([pw0,pw1,pw2,pw4,pw10,pw21,pw83],[8,1,117,65,5,21,29,56,88,33,13,61,69,77,3,16,20,9,41,45,53,57,81,85,89,145,173,177],[131094,1035,19,19,19,1027,33554956,262692,544773,82436,3145796,67110952,137,1,134225992,4194561,2336,8388960,128,16781313,41152]),
([pw108,pw0,pw1,pw2,pw4,pw10,pw83],[56,8,92,13,29,61,5,77,117,145,20,21,25,41,49,57,65,69,105,109,113,3],[11,2098433,3,37,131075,145,74,11,2054,74,11,66049,8484,20482,32785,37,515,145,262150,524293,1048579]),
([pw0,pw1,pw2,pw4,pw10,pw83,pw109],[12,56,1,117,73,96,5,13,33,3,16,21,25,77,177,20,9,29,41,45,49,53,61,69,81,109,165],[65612,149,69,69,133,133,794,264456,1576968,2105865,33546,16402,16402,19,1,16783392,33554465,4194338,67118081,8389634,131074]),
([pw110,pw0,pw1,pw2,pw4,pw10,pw83],[56,12,16,100,117,29,61,69,3,1,5,73,20,41,49,57,77,85,105,113,181,185],[259,4369,3,73,133,65537,1538,1048579,522,1030,2097187,2321,8280,16532,32801,73,133,2051,262156,131081,524325])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p16_D6 : List StD := [
([pw1,pw11,pw2,pw13,pw4,pw10,pw83],[21,29,5,13,25,97,193,61,69,56,104,108,41,57,101,105,109,113,117,121,125,129,181,189,197,201,3],[262144,75497504,2097220,16777281,524368,33554498,4194344,1036,137,280,522,16384,161,304,1048610,4101,2052,8198,32785,65539,131090]),
([pw0,pw135,pw11,pw2,pw4,pw10,pw83],[21,29,69,37,129,3,9,25,12,33,61,1,101,105,109,113,117,125,137,193,205,209,213],[524608,2048,56,1048593,148,2097170,65536,4096,97,100,290,262664,1025,132,4194818,1033,140,131082,8197,16387,32774]),
([pw104,pw0,pw11,pw2,pw4,pw10,pw83],[61,69,77,9,129,21,25,29,33,101,112,1,37,105,109,113,117,149,189,193,209,213],[524312,66568,4096,41,74,140,2048,262672,49,82,1048596,131840,33,66,2097412,33,66,132,8195,16389,32774]),
([pw0,pw1,pw2,pw23,pw4,pw10,pw83],[29,41,69,101,117,3,16,21,25,57,4,1,5,33,37,97,105,109,113,121,125,137,193,217,221,225],[12582928,16809992,2048,130,260,4609,2097176,8192,146,524308,529,16384,33554442,268,1048585,1058,100,97,65542,131075,262149]),
([pw24,pw0,pw1,pw2,pw4,pw10,pw83],[13,21,5,69,77,117,61,112,25,29,33,37,101,105,109,113,121,149,197,201],[5,1184,4096,194,264,528,5,5,67,5,5,133152,262178,65576,524336,66,264,528,8202,16402,32792]),
([pw113,pw0,pw1,pw11,pw2,pw4,pw10],[25,101,5,21,57,37,69,9,61,29,116,97,105,121,185,193,197,213],[532,528,1024,50,280,81,32900,16384,2054,268,69,131072,34,65672,8321,34,264,65,34,67,4105]),
([pw113,pw0,pw1,pw2,pw4,pw10],[120,57,61,185,213,37,69,5,9,21,25,101,29,17,41,49,65,77,81,93,229,233],[4234,4370,133154,519,525378,408,1056808,525,1224,2352,16405,2130000,2565,66656,262149]),
([pw0,pw1,pw2,pw137,pw4,pw10,pw83],[25,117,13,21,29,101,1,124,61,77,17,33,69,105,109,113,121,137,157,161,193,197,201,217,221],[9437186,16777252,68,68,524293,68,131106,2178,2097162,65539,4194322,1024,296,262177,560,392,4097,528,8201,16408,32785]),
([pw0,pw1,pw2,pw4,pw138,pw83],[1,41,57,69,101,237,9,21,29,241,128,13,17,25,37,49,61,73,77,85,89,245],[609,6161,643,8713,2309,16496,226,32872,2097444,81938,12312,393236,1162,525318,1048844]),
([pw104,pw92,pw0,pw2,pw4,pw10,pw83],[61,69,77,13,9,21,25,29,57,101,249,33,37,41,105,109,113,117,129,217,237],[131072,524312,4096,49,82,148,262144,1536,8193,1050626,260,1544,41,74,268,33,66,132,16387,32773,65542]),
([pw0,pw135,pw1,pw13,pw4,pw10,pw83],[21,25,57,33,181,3,17,29,12,37,1,41,97,101,105,109,113,117,121,137,253,257,261,265],[4416,56,1024,1048593,2097170,148,131072,8192,97,98,292,524808,4194313,262154,140,2049,8389122,132,16387,32773,65542]),
([pw86,pw0,pw1,pw13,pw4,pw10,pw83],[41,49,57,17,181,21,29,25,37,117,132,1,33,97,101,105,109,113,149,189,257,265],[8216,4096,17416,41,138,76,524816,2048,49,1048594,84,262912,33,130,68,33,2097410,68,32771,65541,131078]),
([pw32,pw0,pw1,pw2,pw4,pw10,pw83],[5,21,13,49,57,101,41,132,25,29,33,37,105,109,113,117,125,149,225,269],[5,32768,2208,194,264,528,5,5,67,5,5,132128,66,264,528,262178,524328,65584,4106,8210,16408]),
([pw35,pw0,pw1,pw2,pw13,pw4,pw83],[29,117,21,69,33,57,17,41,25,136,13,97,109,125,161,193,217,225,265],[264,26,264,512,140,41,98306,3136,16384,132,33,18,18,18,35,262144,131140,8257,132,33,4101]),
([pw35,pw0,pw1,pw2,pw4,pw83],[140,41,69,161,265,33,57,13,17,21,29,117,25,9,49,53,61,77,85,89,241,273],[4236,18468,4372,519,525380,1056808,408,523,1224,2352,2563,33888,65555,2228304,262147]),
([pw0,pw1,pw139,pw2,pw4,pw10,pw83],[5,29,101,41,49,117,1,21,25,57,144,9,37,97,105,109,113,125,137,185,217,225,269],[1048609,65,8197,65,65,524291,2048,262180,168,304,546,5124,136,272,514,2097164,4194324,131078,16408,32778,65554]),
([pw0,pw1,pw2,pw4,pw10,pw140],[1,41,57,69,117,277,17,5,25,148,9,21,29,33,61,229,45,49,77,81,93,281],[1169,32865,2179,393,36869,8304,10258,196632,5140,16482,2097448,262244,524810,16902,1048844]),
([pw86,pw101,pw0,pw1,pw4,pw10,pw83],[41,49,57,5,17,21,29,25,69,117,249,33,37,61,101,105,109,113,181,221,277],[16384,524312,2048,49,146,84,262144,1536,8193,258,1052676,1544,41,266,76,33,130,68,32771,65541,131078]),
([pw0,pw1,pw141,pw2,pw4,pw10,pw83],[33,57,69,37,9,41,17,25,29,21,1,97,105,109,113,121,125,193],[131089,1024,2120,544,132,258,17,17,17,32773,259,72,544,132,258,72,140,65546,4132,8226,16390]),
([pw1,pw141,pw2,pw4,pw10,pw83],[1,21,25,29,33,37,5,97,193,104,13,41,57,69,45,49,53,61,65,73,77,81,85,89,93],[337,432,2322,49172,69656,1185,2115,8261,5129,131234,270372,1572904,2097670,4194826,25165836]),
([pw0,pw1,pw2,pw142,pw10,pw83],[56,20,1,33,37,5,29,152,41,57,65,69,3,13,21,25,45,53,81,93,109,125,137],[4142,12309,16676,34852,581,4194315,131082,65546,523,1041,1041,2097233,264576,1048705,524353]),
([pw0,pw1,pw2,pw4,pw143,pw83],[56,20,1,33,37,5,29,157,156,41,57,69,3,13,21,25,45,53,81,93,109,125],[4142,12309,16932,34852,1093,139,131082,65546,1035,145,145,2097233,264960,1048833,524353]),
([pw0,pw1,pw2,pw4,pw10,pw144],[56,20,1,33,37,5,29,160,41,57,65,69,3,13,21,25,45,53,81,93,109,125,137],[4142,12309,16676,34852,581,4194315,131082,65546,523,1041,1041,2097233,264576,1048705,524353]),
([pw52,pw0,pw1,pw2,pw4,pw10,pw83],[9,17,21,25,29,41,57,69,101,117,5,105,109,113,121,125,137,225],[1024,513,258,36,136,80,513,258,36,136,80,65539,37,16393,81,131078,138,32786,2060,4116,8216]),
([pw0,pw2,pw19,pw4,pw10,pw105,pw83],[29,41,1,101,49,45,61,77,117,133,164,21,25,37,57,97,105,109,113,121,129,157,185,221,285,289,293],[8421384,17825796,33554438,516,516,4194309,8192,74,2097176,67109128,137,2050,524336,1312,129,65554,66,131075,4096,262161,16385]),
([pw136,pw0,pw2,pw19,pw4,pw10,pw83],[41,57,137,117,21,25,29,1,101,33,37,49,61,69,77,81,97,109,129,161,165,193,217,221,285],[6291464,268,512,25,2048,74,8454148,17039488,17,524448,66,1024,4101,260,16390,17,8224,66,32769,131075,1048610]),
([pw0,pw1,pw19,pw4,pw10,pw83,pw109],[1,41,49,117,5,77,101,21,25,73,297,168,29,33,61,105,109,125,137,157,165,193,217,301,305],[6291464,17,17,17,1025,1025,8192,138,268,25165832,262216,130,260,131616,2624,32774,65570,16386,1048612,524356,4096]),
([pw110,pw0,pw1,pw19,pw4,pw10,pw83],[25,61,117,29,101,1,21,5,49,57,33,37,41,77,85,97,105,113,137,157,185,193,217,221],[8421392,262164,2048,82,524305,8192,6291460,160,66,161,1048616,1024,4102,261,524,66,257,520,65539,16386,131081]),
([pw0,pw1,pw2,pw4,pw10,pw145,pw83],[29,41,101,117,1,21,69,57,65,133,25,33,37,61,77,97,105,109,113,121,185,193,217,221],[6291464,8421380,34,528,528,1048593,268,42,524360,2048,137,8198,260,4096,16389,65602,34,131075,1024,262209,129]),
([pw146,pw0,pw1,pw2,pw4,pw10,pw83],[1,45,29,13,21,65,117,57,101,25,41,49,61,77,81,93,109,161,193],[9,66,288,1040,2048,132,262147,9,9,131585,9,66,66,66,134,4144,288,8228,16400,65556,32772]),
([pw0,pw1,pw2,pw4,pw10,pw83,pw147],[25,41,101,117,1,21,57,49,297,29,33,37,53,61,97,105,109,113,125,137,157,161,193,201,217,221],[20971528,33570820,34,2097169,272,272,524300,42,137,8392712,1024,8198,1048581,262212,2048,32771,65602,34,131137,129,512]),
([pw148,pw0,pw1,pw2,pw4,pw10,pw83],[1,25,53,73,5,21,101,117,41,49,29,57,85,89,97,105,157,185],[17,132,72,288,514,2048,17,16393,17,17,132097,132,292,518,132,72,65546,72,32802,4128,8194]),
([pw0,pw149,pw1,pw2,pw4,pw10,pw83],[29,37,69,117,41,17,25,9,21,57,56,1,5,61,105,109,113,121,125,3],[2048,136,34,272,68,4609,136,34,8208,68,525313,42,280,131084,521,34,70,262147,16404,32785,65541]),
([pw0,pw1,pw2,pw4,pw10,pw83,pw150],[25,37,41,117,1,21,49,53,73,297,29,57,85,105,113,149,161,181,193,201,217,269,289,309],[1310728,131090,4194324,65553,528,528,32778,44,73,524424,136,8388614,2097155,258,258,8197,4100,36,18433,65,1024]),
([pw0,pw151,pw1,pw2,pw4,pw10,pw83],[33,57,69,41,101,9,29,17,21,25,16,1,105,109,113,121,125,225,3],[2048,33,144,264,516,66,33,144,264,263172,66,33,33,32773,67,131096,532,65554,4108,8202,16390]),
([pw0,pw1,pw2,pw4,pw10,pw152,pw83],[1,29,33,41,101,45,61,65,77,133,21,25,69,81,97,109,129,149,165,185,201,269,289],[65541,16401,4194313,513,513,524291,131092,1036,36,36,1048582,88,2097296,144,274,8200,72,32778,2048,266242,258]),
([pw0,pw1,pw2,pw4,pw105,pw21,pw83],[1,21,57,13,65,49,29,41,45,61,69,77,156,101,109,117,121,129,133,157,269,285],[2228225,9,9,262145,9,9,524304,130,32768,65824,324,530,1049616,8192,2068,130,514,16390,5152,68,2084]),
([pw153,pw1,pw2,pw4,pw10,pw83],[1,37,45,61,69,93,193,5,29,101,172,13,21,25,41,65,73,77,81,85,89,153,241],[197,2563,4233,8337,2337,582,16460,4194388,2097444,4618,40978,196642,263192,525352,1048880]),
([pw0,pw1,pw2,pw154,pw4,pw10,pw83],[117,25,57,1,45,61,101,13,21,29,69,37,77,81,97,109,161,165,193,217,221],[786433,1065024,136,136,65546,136,17,17,17,17,517,2048,352,1090,4164,288,1026,516,8226,32804,131078]),
([pw0,pw1,pw2,pw4,pw10,pw106,pw109],[1,41,49,5,53,21,25,57,61,69,77,160,73,101,105,117,125,181,201,297,301,313],[9,2228225,9,9,9,524289,1048592,50,84,32768,262288,258,516,70656,8192,16390,34,258,68,516,3200]),
([pw155,pw0,pw1,pw2,pw4,pw10,pw83],[1,21,25,77,117,5,53,57,41,49,13,37,101,105,109,113,225,269,309],[33,80,4096,258,516,136,33,1025,33,33,137,80,274,532,80,327682,133124,136,8198,16394,32780]),
([pw0,pw1,pw2,pw156,pw4,pw10,pw83],[117,29,41,49,101,1,5,21,25,53,77,37,61,97,105,109,137,157,165,185,193,217,221],[3145729,4202512,96,96,96,524322,65553,513,133,265,513,2048,4116,131096,1042,132,264,1026,16396,32774,262154]),
([pw130,pw0,pw1,pw2,pw4,pw10,pw83],[1,29,101,21,49,65,133,61,69,77,5,33,97,105,109,113,117,185,197,201,261],[65,65536,36,136,272,514,1025,4101,65,65,131075,36,1310728,272,526338,140,36,518,8216,16394,32786]),
([pw0,pw1,pw157,pw2,pw4,pw10,pw83],[29,101,1,41,117,49,5,65,21,25,57,33,61,77,97,105,109,113,185,193,217],[1572880,68,16390,68,68,262149,2048,146,280,560,1041,130,264,544,1025,4106,130,8195,32808,65545,131105]),
([pw158,pw1,pw2,pw4,pw10,pw83],[1,33,41,57,73,89,97,5,25,117,176,13,21,29,45,49,53,61,81,85,93,177,229],[643,2129,4229,417,10249,594,4614,49186,73738,131156,2097456,4194392,263204,525324,1048872]),
([pw0,pw1,pw125,pw2,pw4,pw10,pw83],[101,1,29,49,117,41,5,73,21,25,57,33,85,97,105,113,137,157,185,193,217],[1572880,66,8195,66,66,262150,2048,65553,304,536,1044,129,288,520,1028,129,131081,129,16424,4132,32780])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p16_D5 : List StD := [
([pw135,pw11,pw13,pw4,pw10,pw83],[21,25,29,33,129,189,3,1,37,101,105,109,113,117,205,209,257,317,321],[8192,512,97,98,100,152,131081,65546,262156,16401,274,32788,1027,2053,4102]),
([pw0,pw11,pw2,pw142,pw10,pw83],[29,37,69,61,129,25,1,9,21,33,105,109,113,125,137,193,205,209,213,325,3],[64,1048594,98320,52,131089,540674,136,36,262657,266,38,8195,1036,2057,4101]),
([pw0,pw11,pw2,pw4,pw143,pw83],[29,37,9,61,157,33,1,21,105,109,113,117,125,129,193,205,209,213,329,333,337,3],[64,2359298,557056,1064960,73729,18,136,2084,131105,18,18,4099,268,521,1029]),
([pw0,pw11,pw2,pw4,pw10,pw144],[21,37,69,9,129,25,33,61,1,101,105,109,113,117,137,193,205,209,3],[256,262162,65553,52,163856,16450,129,36,8264,131,38,522,1029,2057,4108]),
([pw59,pw0,pw1,pw2,pw10,pw83],[21,25,29,101,289,117,41,57,97,105,109,113,193,225,241,261,341,345,349],[81,65,8201,515,1029,4144,280,16402,148,32808,65570,132,131082,262156,2054]),
([pw60,pw0,pw1,pw2,pw4,pw83],[21,25,29,101,117,161,41,57,1,33,37,97,105,109,113,193,225,265,353],[290,530,1034,4099,16390,32816,2088,97,164,131096,81,148,65545,262156,8197]),
([pw159,pw0,pw1,pw2,pw4,pw10],[21,101,185,25,29,117,5,41,33,37,97,105,109,113,121,137,225,269],[68,304,530,4113,8216,68,1030,133,68,32802,161,16424,65539,131082,2057]),
([pw0,pw1,pw13,pw142,pw10,pw83],[25,33,57,21,181,29,1,37,41,97,105,109,113,117,121,137,253,257,265,325,3],[1048594,64,66064,131089,52,557058,8202,16387,38,264,262273,36,1033,2060,4101]),
([pw0,pw1,pw13,pw4,pw143,pw83],[21,33,57,181,17,29,37,157,1,97,105,109,113,117,253,257,261,3],[131082,256,16393,33288,44,194,65539,8210,38,193,192,36,1041,2053,4116]),
([pw0,pw1,pw13,pw4,pw10,pw144],[33,41,17,25,21,37,1,97,101,105,109,113,117,121,137,257,265,321,357,361,3],[1310721,64,18,557056,131200,16417,19,8201,4101,18,65576,292,522,1030,2060]),
([pw160,pw0,pw1,pw2,pw4,pw10],[37,185,17,61,69,117,5,21,25,9,101,105,121,197],[66,544,1029,136,272,66,7,138,66,37,8232,4144,5,273,2072]),
([pw161,pw0,pw1,pw2,pw4,pw83],[17,21,25,29,33,161,41,57,9,101,1,109,117,225,353],[1060,4116,517,70,140,304,545,98,168,273,82,152,8195,16393,2058])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p16_D4 : List StD := [
([pw11,pw13,pw142,pw10,pw83],[29,33,129,189,25,37,101,105,109,113,209,257,317,321,325],[16390,4106,2066,8195,76,36,1029,152,265,529]),
([pw11,pw13,pw4,pw143,pw83],[21,29,33,157,189,1,37,105,109,113,117,205,209,317,321],[44,8197,1044,16390,2057,72,4106,145,259,530]),
([pw11,pw13,pw4,pw10,pw144],[21,33,129,189,25,1,37,101,105,109,113,117,205,257,317],[38,16387,8210,2058,4101,68,140,273,521,1048])]
def p16_D3 : List StD := []
theorem p16_I3 : LevelN true p16_T 3 p16_D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p16_C4x0 : levelOK true p16_T p16_t 3 (p16_D3.map Prod.fst) ((p16_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p16_I4 : LevelN true p16_T 4 p16_D4 := levelStep p16_B p16_W p16_I3 (chunks 32 p16_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p16_C4x0
  ))
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
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p16_C6x1 : levelOK true p16_T p16_t 5 (p16_D5.map Prod.fst) ((p16_D6.drop (1*32)).take 32) = true := by decide +kernel
theorem p16_I6 : LevelN true p16_T 6 p16_D6 := levelStep p16_B p16_W p16_I5 (chunks 32 p16_D6 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p16_C6x0
  · exact p16_C6x1
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
def p17_T : Nat := 0xeaeaeac8eaeaeac8eaeaeac8eaeaeac8eaeaeac8eaeaeac8eaeaeac8eaeaeac8
def p17_R : List Nat := [0, 1, 2, 3, 4]
def p17_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,1,9),(4,1,17)]
theorem p17_B : baseOK p17_T p17_R p17_E = true := by decide +kernel
def p17_Z : List SliceD := [(pw3,4,[0, 1, 2, 4])]
theorem p17_Y : ∀ s ∈ p17_Z, SliceN true p17_R p17_T s := by
  unfold p17_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p17_B p5_B p5_L (by decide +kernel),by simp⟩
def p17_C : List (Nat × List Nat) := [(0,[])]
def p17_t : Tabs := (p17_C.map (mkCut true p17_Z),[(6,4),(3,1),(3,2),(9,12),(6,2),(9,1),(9,0),(17,1),(17,0),(6,12),(6,20),(9,5),(17,5)],[],[[]])
theorem p17_W : TabsP true p17_R p17_T p17_t := ⟨cutsGood p17_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p17_D4 : List StD := [
([pw0,pw1,pw2,pw4,pw10],[1,21,9,17,29,5,0,13,25,33,37,41,45,49],[33,140,262,532,33,1027,2065,4106,8216,66])]
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
theorem p17_L : LowN true p17_R p17_T 5 := lowSearch p17_B p17_I4 (by decide +kernel)
def p18_T : Nat := 0xeaeaeae8eaeaeae8eaeaeae8eaeaeae8eaeaeae8eaeaeae8eaeaeae8eaeaeae8
def p18_R : List Nat := [0, 1, 2, 3, 4]
def p18_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,1,17)]
theorem p18_B : baseOK p18_T p18_R p18_E = true := by decide +kernel
def p18_Z : List SliceD := [(pw3,5,[0, 1, 2, 4])]
theorem p18_Y : ∀ s ∈ p18_Z, SliceN true p18_R p18_T s := by
  unfold p18_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p18_B p2_B p2_L (by decide +kernel),by simp⟩
def p18_C : List (Nat × List Nat) := [(0,[])]
def p18_t : Tabs := (p18_C.map (mkCut true p18_Z),[(5,4),(6,4),(3,2),(3,1),(6,2),(5,1)],[],[[]])
theorem p18_W : TabsP true p18_R p18_T p18_t := ⟨cutsGood p18_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p18_D5 : List StD := [
([pw0,pw1,pw2,pw4,pw10],[0,1,5,17,9,13,21],[54,90,3,3,108,5,5,9,9,1])]
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
def p19_T : Nat := 0xfeeefaeafeeefac8feeefaeafeeefac8feeefaeafeeefac8feeefaeafeeefac8
def p19_R : List Nat := [0, 1, 2, 3, 4, 5]
def p19_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,1,9),(4,1,17),(5,1,33)]
theorem p19_B : baseOK p19_T p19_R p19_E = true := by decide +kernel
def p19_Z : List SliceD := [(pw5,5,[0, 3, 2, 4, 5]),(pw131,4,[1, 2, 3, 4]),(pw6,6,[0, 1, 4, 3, 5]),(pw3,6,[0, 1, 4, 2, 5]),(pw7,5,[0, 2, 1, 3, 5]),(pw91,6,[0, 1, 2, 3, 4]),(pw8,4,[0, 3, 2, 5]),(pw97,4,[1, 2, 3, 4])]
theorem p19_Y : ∀ s ∈ p19_Z, SliceN true p19_R p19_T s := by
  unfold p19_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p19_B p17_B p17_L (by decide +kernel),mkSlice (w:=0) p19_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p19_B p18_B p18_L (by decide +kernel),mkSlice (w:=0) p19_B p13_B p13_L (by decide +kernel),mkSlice (w:=0) p19_B p15_B p15_L (by decide +kernel),mkSlice (w:=0) p19_B p8_B p8_L (by decide +kernel),mkSlice (w:=0) p19_B p5_B p5_L (by decide +kernel),mkSlice (w:=32) p19_B p5_B p5_L (by decide +kernel),by simp⟩
def p19_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(3,[385]),(5,[257]),(2,[512]),(3,[514]),(2,[389]),(5,[389]),(4,[393]),(3,[517]),(2,[521]),(3,[521]),(3,[519]),(2,[389,533])]
def p19_t : Tabs := (p19_C.map (mkCut true p19_Z),[(6,4),(3,2),(3,1),(17,20),(6,2),(9,1),(9,0),(17,16),(17,1),(33,1),(33,0),(18,24),(18,16),(18,2),(6,36),(9,5),(28,24),(33,5),(28,20),(12,36),(18,34),(6,5),(9,8),(11,2),(35,2),(7,1),(12,8),(12,4),(17,5),(18,10),(33,36),(9,24),(49,16),(37,5),(37,4),(21,5),(21,20),(18,56),(18,48),(26,56),(26,10),(26,24),(26,42),(3,4),(9,10),(12,1),(9,4),(17,4),(3,8),(12,2),(6,8),(18,8),(50,24),(17,0),(18,32),(33,4),(38,2),(12,0),(44,0),(37,1),(6,0),(12,32),(9,2),(33,34),(12,16)],[],[[]])
theorem p19_W : TabsP true p19_R p19_T p19_t := ⟨cutsGood p19_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p19_D7 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw83],[4,3,0,8,12,20,1,5,17,21,37,16,9,33,24,13,25,29,41,45,49,53,57,61,65,69,73,77,81],[4295,33163,66193,141443,263331,4428,524886,3162180,4195430,8388632,16777480,33554473,67109392,134217777,268446755])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p19_D6 : List StD := [
([pw0,pw1,pw11,pw2,pw4,pw10,pw83],[17,33,28,5,9,21,3,37,53,105,16,20,1,85,89,93,97,101,109,113,117],[8216,16384,73,32808,266,65672,4096,131089,112,274,20,513,262176,1090,2180,513,524291,5,1048610,36,6]),
([pw0,pw1,pw13,pw4,pw10,pw83],[28,32,1,21,13,36,105,3,33,37,49,53,121,8,9,17,45,65,73],[16533,8192,27,4113,4113,33860,65678,3332,549,202,133440,33,262154,11,545]),
([pw0,pw1,pw2,pw4,pw10,pw17,pw83],[1,21,17,37,29,9,33,109,28,20,5,13,45,49,53,57,65,69,73,77,113,125,129],[33,2068,146,2097232,1024,4194328,33,4099,8193,33,32777,134,1048644,65540,131084,262146,130,524298,16384,320,776]),
([pw103,pw0,pw1,pw2,pw4,pw10],[28,44,21,1,33,37,97,3,40,9,105,20,17,41,45,49,53,65,73,109,129,133,137,141],[2304,681,2097409,39,177,8257,4194369,7,1048641,5640,16526,98328,524294,8520720,262150]),
([pw0,pw1,pw2,pw20,pw10,pw83],[48,52,17,89,3,0,45,53,109,145,33,37,12,24,56,5,21,41,65,69,73,77,81,149],[32888,541,66312,1672,133146,101,4096,16608,8388706,277,262149,524295,1049984,2099474,4202626]),
([pw0,pw1,pw2,pw4,pw10,pw106],[28,24,89,21,57,5,105,141,17,37,145,153,60,9,33,109,133,157,161],[53,1029,37,1029,37,2384,131098,2066,8195,33096,16578,66049,262282,4617,131]),
([pw0,pw1,pw2,pw4,pw10,pw112],[28,24,1,17,89,21,145,64,5,9,105,165,68,33,37,65,81,109,169],[788,89,273,81,81,1548,2086,2054,7,132136,32906,137,327714,20513,8195])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p19_D5 : List StD := [
([pw1,pw11,pw13,pw4,pw10,pw83],[28,5,53,9,21,33,105,13,117,121,173,177,181,185,189,3],[1024,2058,32792,44,9,66,12288,16900,129,82,38,3,276,17,5]),
([pw0,pw11,pw2,pw20,pw10,pw83],[9,33,37,5,17,53,109,24,45,69,77,81,85,97,113,193,197,201,205,209,3],[32768,1048600,4105,42,8204,196608,65,262274,524548,81,16402,532,35,1029,2054]),
([pw27,pw0,pw1,pw2,pw4,pw83],[17,37,213,9,21,33,105,5,109,1,69,77,81,97,189,205,217],[132,552,97,304,4130,132,16389,276,8198,73,32792,65546,65,1027,2066]),
([pw0,pw1,pw13,pw20,pw10,pw83],[37,53,13,21,33,45,17,3,5,9,77,81,149,185,201,221,225],[164,256,8204,22,32773,16480,512,50,4129,200,18,65601,26,1033,2051]),
([pw33,pw0,pw1,pw13,pw10,pw83],[9,37,21,33,49,53,13,17,25,57,77,81,181,185,221,229,233],[12292,21,128,44,1030,17,256,40,16450,17,17,515,40,98306,2058]),
([pw0,pw1,pw162,pw2,pw4,pw10],[5,17,33,9,21,53,105,3,1,37,41,85,93,101,109,113,117,221],[2057,1025,131075,4113,37,256,8202,152,44,66,16400,644,66,32774,65556]),
([pw0,pw1,pw2,pw4,pw10,pw163],[1,21,17,29,9,109,33,13,41,45,49,53,65,73,113,125],[17,140,42,32840,264,17,515,1025,17,38,16452,4100,8194,34,2048]),
([pw103,pw0,pw1,pw2,pw20,pw10],[17,33,21,37,45,53,109,97,5,9,41,113,201,221,237,3],[256,32792,16393,76,42,1168,8321,68,34,4113,512,50,69,2051,38]),
([pw90,pw0,pw1,pw20,pw10,pw83],[5,37,17,29,53,33,21,41,45,81,149,197,201,225,229,241,245],[13,6148,64,52,8198,9,9,9,131,32768,48,1282,48,81922,530]),
([pw0,pw1,pw2,pw20,pw10,pw164],[5,17,33,29,53,72,76,13,57,113,193,197,201,237,245,249],[33793,131,9,9,9,6144,256,20,32,16450,518,8258,20,32,20])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p19_D4 : List StD := [
([pw11,pw13,pw20,pw10,pw83],[33,5,37,9,53,121,13,77,81,97,173,181,189,193,197,253],[24576,3072,4129,96,32778,19,518,17,140,261]),
([pw0,pw1,pw165,pw10,pw83],[21,29,37,49,53,5,17,33,41,81,153,213,245,253,257],[8202,35,2066,262,73,152,1036,16401,4101,532]),
([pw0,pw162,pw2,pw20,pw10],[5,9,17,45,33,53,109,37,85,113,193,201,221],[1033,4101,259,49,2060,74,136,70,532,50]),
([pw166,pw0,pw1,pw2,pw4],[17,213,9,21,33,105,5,109,1,189,205],[66,276,49,152,66,515,138,37,1036,33])]
def p19_D3 : List StD := []
theorem p19_I3 : LevelN true p19_T 3 p19_D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p19_C4x0 : levelOK true p19_T p19_t 3 (p19_D3.map Prod.fst) ((p19_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p19_I4 : LevelN true p19_T 4 p19_D4 := levelStep p19_B p19_W p19_I3 (chunks 32 p19_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p19_C4x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p19_C5x0 : levelOK true p19_T p19_t 4 (p19_D4.map Prod.fst) ((p19_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p19_I5 : LevelN true p19_T 5 p19_D5 := levelStep p19_B p19_W p19_I4 (chunks 32 p19_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p19_C5x0
  ))
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
theorem p19_L : LowN true p19_R p19_T 8 := lowSearch p19_B p19_I7 (by decide +kernel)
def p20_T : Nat := 0xeeeaece0eeeaece0eeeaece0eeeaece0eeeaece0eeeaece0eeeaece0eeeaece0
def p20_R : List Nat := [0, 1, 2, 3, 4]
def p20_E : List (Nat × Nat × Nat) := [(0,4,5),(1,4,6),(2,1,5),(3,2,10),(4,1,17)]
theorem p20_B : baseOK p20_T p20_R p20_E = true := by decide +kernel
def p20_Z : List SliceD := []
theorem p20_Y : ∀ s ∈ p20_Z, SliceN true p20_R p20_T s := by
  intro s h
  cases h
def p20_C : List (Nat × List Nat) := []
def p20_t : Tabs := (p20_C.map (mkCut true p20_Z),[(5,4),(10,9),(6,4),(6,2),(5,0),(10,3),(10,2),(17,1),(17,0),(5,1),(10,0),(17,3),(5,9),(6,18),(17,9)],[],[[]])
theorem p20_W : TabsP true p20_R p20_T p20_t := ⟨cutsGood p20_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p20_D4 : List StD := [
([pw0,pw1,pw2,pw4,pw10],[1,9,13,25,29,5,17,21,33,37,41,45,49,53,57],[35,69,137,273,518,1034,2066,4108,8212,16408])]
def p20_D3 : List StD := []
theorem p20_I3 : LevelN true p20_T 3 p20_D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p20_C4x0 : levelOK true p20_T p20_t 3 (p20_D3.map Prod.fst) ((p20_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p20_I4 : LevelN true p20_T 4 p20_D4 := levelStep p20_B p20_W p20_I3 (chunks 32 p20_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p20_C4x0
  ))
theorem p20_L : LowN true p20_R p20_T 5 := lowSearch p20_B p20_I4 (by decide +kernel)
def p21_T : Nat := 0xfefefeeefefafc88fefefeeefefafc88fefefeeefefafc88fefefeeefefafc88
def p21_R : List Nat := [0, 1, 2, 3, 4, 5]
def p21_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,8,12),(3,2,10),(4,1,17),(5,1,33)]
theorem p21_B : baseOK p21_T p21_R p21_E = true := by decide +kernel
def p21_Z : List SliceD := [(pw6,6,[0, 1, 5, 3, 4]),(pw2,6,[3, 4, 0, 1, 5]),(pw3,7,[4, 0, 1, 5, 2]),(pw7,7,[3, 1, 0, 5, 2]),(pw91,7,[0, 2, 3, 1, 4]),(pw84,5,[1, 2, 3, 4, 5]),(pw5,5,[0, 2, 4, 3, 5])]
theorem p21_Y : ∀ s ∈ p21_Z, SliceN true p21_R p21_T s := by
  unfold p21_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p21_B p13_B p13_L (by decide +kernel),mkSlice (w:=4) p21_B p9_B p9_L (by decide +kernel),mkSlice (w:=0) p21_B p7_B p7_L (by decide +kernel),mkSlice (w:=0) p21_B p7_B p7_L (by decide +kernel),mkSlice (w:=0) p21_B p14_B p14_L (by decide +kernel),mkSlice (w:=0) p21_B p20_B p20_L (by decide +kernel),mkSlice (w:=0) p21_B p20_B p20_L (by decide +kernel),by simp⟩
def p21_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(2,[262]),(5,[]),(2,[263]),(2,[260]),(3,[260]),(4,[384]),(6,[]),(2,[261]),(4,[385]),(3,[261]),(3,[263]),(4,[386]),(3,[262]),(4,[387]),(2,[261,404])]
def p21_t : Tabs := (p21_C.map (mkCut true p21_Z),[(17,16),(10,8),(3,2),(3,1),(12,8),(13,9),(13,5),(10,2),(17,1),(20,4),(33,1),(34,2),(22,18),(22,6),(33,5),(17,9),(33,9),(34,18),(10,9),(37,36),(12,5),(38,36),(20,6),(12,4),(37,5),(7,6),(19,18),(7,5),(3,0),(3,9),(25,24),(26,24),(20,16),(44,40),(26,18),(25,9),(44,36),(41,9),(52,36),(50,18),(3,18),(33,0),(34,0),(3,5),(41,8),(11,9),(50,16)],[],[[]])
theorem p21_W : TabsP true p21_R p21_T p21_t := ⟨cutsGood p21_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p21_D8 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw83],[0,4,8,12,16,17,33,41,25,29,37,45,1,5,9,13,21,49,53,57,61,65,69,3],[8450048,65571,772,1096,2192,131107,772,262216,2192,39,1131,524467,1048588,2097172,4194328])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p21_D7 : List StD := [
([pw167,pw0,pw1,pw2,pw4,pw10,pw83],[24,32,36,40,44,3,20,1,5,77,85,0,4,28,29,33,37,41,61,65,69,73,81,89,93,97],[65,8193,6145,99,37,41,2097169,641,4194307,133,521,1296,274,8388628,1048,16793602,98308,33685512,262150,524298,1048588]),
([pw0,pw1,pw11,pw2,pw4,pw10,pw83],[24,44,48,52,9,13,33,56,21,25,41,29,45,49,53,0,4,17,37,61,65,69,73,93,97,101,105,109,3],[4194355,2,33554705,2581,67108945,5145,1,134225954,2598,16610,5162,229632,8389124,262336,268436488,2564,24896,16778504,524420,1048588,2097352]),
([pw12,pw0,pw1,pw2,pw4,pw10,pw83],[24,20,44,60,64,25,33,41,32,9,29,53,0,4,48,5,45,49,61,65,69,85,97,101,113],[260,16385,12289,291,73,145,16777733,8389121,35,73,145,2260996,1062,2124,65684,1058,2120,4194448,262154,524306,1048600]),
([pw92,pw0,pw1,pw2,pw4,pw10,pw83],[44,28,68,72,29,45,53,24,48,13,25,33,0,4,1,5,21,41,61,65,69,77,97,109,113],[257,32769,12289,275,69,41,16777857,2179200,1042,2116,131112,8389121,19,69,41,1042,2116,4194344,262150,524298,1048588])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p21_D6 : List StD := [
([pw0,pw1,pw2,pw168,pw10,pw83],[44,1,5,17,29,37,45,77,85,25,33,129,21,41,97,117,121,125,133,137,141,145,149,153,157],[32775,4234,66066,1186,8386,261,261,131077,261,2584,3112,278600,1572912,6291536,25165920]),
([pw0,pw1,pw2,pw4,pw169,pw83],[24,1,5,17,33,41,93,49,77,85,29,53,45,97,121,125,133,137,141,145,149,153,157,161],[8388615,259,16387,259,259,652,1604,34836,4644,1224,2200,73768,393296,1572960,6291504]),
([pw0,pw1,pw2,pw4,pw10,pw170],[24,44,1,5,29,33,41,77,85,129,17,37,73,93,97,121,125,133,137,141,145,149,153,157],[4111,133,32773,133,133,266,266,65546,266,9744,3616,148032,786480,3145808,12583008]),
([pw113,pw0,pw1,pw11,pw2,pw4,pw10],[21,29,33,9,45,37,93,17,13,41,76,25,53,61,73,165,169,173],[536,528,1024,145,82,52,16648,32768,137,2058,44,65536,131329,66,4100,129,66,36,67,37,8198]),
([pw113,pw0,pw1,pw2,pw4,pw10],[17,37,45,93,165,169,29,33,49,9,13,21,41,25,53,97,101,105,109,137,141,149,157,177,181,185],[4628,5156,34821,2097228,4194438,1584,67601,8396824,131218,262433,16777320,33570850,329,387,1572874])]
def p21_D5 : List StD := []
theorem p21_I5 : LevelN true p21_T 5 p21_D5 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p21_C6x0 : levelOK true p21_T p21_t 5 (p21_D5.map Prod.fst) ((p21_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p21_I6 : LevelN true p21_T 6 p21_D6 := levelStep p21_B p21_W p21_I5 (chunks 32 p21_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p21_C6x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p21_C7x0 : levelOK true p21_T p21_t 6 (p21_D6.map Prod.fst) ((p21_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p21_I7 : LevelN true p21_T 7 p21_D7 := levelStep p21_B p21_W p21_I6 (chunks 32 p21_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p21_C7x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p21_C8x0 : levelOK true p21_T p21_t 7 (p21_D7.map Prod.fst) ((p21_D8.drop (0*32)).take 32) = true := by decide +kernel
theorem p21_I8 : LevelN true p21_T 8 p21_D8 := levelStep p21_B p21_W p21_I7 (chunks 32 p21_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p21_C8x0
  ))
theorem p21_L : LowN true p21_R p21_T 9 := lowSearch p21_B p21_I8 (by decide +kernel)
def p22_T : Nat := 0xfffffffffffffeeefffafff0ffeaf0c0fffffffffffffeeefffafff0ffeaf0c0
def p22_R : List Nat := [0, 1, 2, 3, 4, 5, 6]
def p22_E : List (Nat × Nat × Nat) := [(0,16,17),(1,4,6),(2,2,6),(3,4,12),(4,1,17),(5,4,36),(6,1,65)]
theorem p22_B : baseOK p22_T p22_R p22_E = true := by decide +kernel
def p22_Z : List SliceD := [(pw84,9,[6, 2, 3, 5, 4, 1]),(pw6,8,[6, 4, 3, 5, 0, 1]),(pw5,9,[3, 5, 6, 4, 0, 2]),(pw91,9,[4, 6, 2, 1, 3, 0]),(pw134,7,[5, 6, 4, 0, 2]),(pw8,7,[6, 5, 3, 2, 0]),(pw171,7,[4, 3, 2, 5, 0]),(pw172,5,[5, 4, 0, 6]),(pw173,5,[6, 4, 0, 5]),(pw174,5,[6, 2, 1, 5, 0]),(pw175,5,[2, 3, 5, 1])]
theorem p22_Y : ∀ s ∈ p22_Z, SliceN true p22_R p22_T s := by
  unfold p22_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p22_B p16_B p16_L (by decide +kernel),mkSlice (w:=0) p22_B p19_B p19_L (by decide +kernel),mkSlice (w:=0) p22_B p10_B p10_L (by decide +kernel),mkSlice (w:=0) p22_B p21_B p21_L (by decide +kernel),mkSlice (w:=0) p22_B p7_B p7_L (by decide +kernel),mkSlice (w:=0) p22_B p7_B p7_L (by decide +kernel),mkSlice (w:=0) p22_B p7_B p7_L (by decide +kernel),mkSlice (w:=4) p22_B p6_B p6_L (by decide +kernel),mkSlice (w:=0) p22_B p2_B p2_L (by decide +kernel),mkSlice (w:=0) p22_B p15_B p15_L (by decide +kernel),mkSlice (w:=1) p22_B p2_B p2_L (by decide +kernel),by simp⟩
def p22_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(0,[261]),(6,[261]),(3,[521]),(7,[]),(8,[]),(5,[393]),(0,[517]),(3,[257]),(0,[129]),(3,[261]),(0,[521]),(3,[513]),(1,[261]),(6,[129]),(9,[]),(0,[257]),(3,[517]),(1,[257]),(5,[257]),(0,[513]),(10,[]),(3,[129]),(4,[261]),(1,[129]),(0,[517,26]),(0,[515]),(0,[131,537]),(0,[131,538]),(0,[512]),(3,[257,154]),(0,[129,666]),(3,[261,410]),(10,[386]),(0,[129,538]),(3,[261,26]),(0,[514]),(0,[518,25]),(0,[257,521]),(3,[513,517]),(4,[262]),(0,[257,537]),(3,[129,537]),(0,[521,26]),(4,[263]),(3,[513,154]),(0,[257,513]),(3,[517,129]),(1,[257,129]),(0,[257,522]),(0,[257,538]),(3,[517,26]),(1,[129,538]),(6,[514]),(3,[129,666]),(4,[261,406])]
def p22_t : Tabs := (p22_C.map (mkCut true p22_Z),[(19,18),(17,16),(21,20),(73,72),(49,48),(12,8),(6,4),(6,0),(74,72),(22,20),(40,10),(6,2),(12,4),(22,18),(21,5),(36,4),(36,0),(76,72),(69,5),(24,16),(24,8),(40,8),(76,68),(73,9),(52,20),(80,64),(80,16),(96,64),(14,10),(66,64),(28,20),(65,1),(6,20),(12,20),(40,32),(36,20),(84,68),(12,68),(84,20),(17,1),(36,68),(65,64),(6,34),(88,72),(12,72),(24,72),(40,72),(80,48),(6,5),(7,4),(12,9),(13,8),(12,5),(13,4),(36,5),(14,8),(6,10),(66,18),(24,18),(65,33),(22,16),(66,0),(82,16),(7,5),(7,3),(25,9),(26,10),(80,72),(6,3),(7,2),(26,18),(42,10),(74,10),(65,72),(73,8),(73,64),(25,8),(66,72),(74,64),(17,3),(17,5),(17,33),(17,2),(21,4),(17,0),(69,4),(65,0),(17,32),(65,32),(19,16),(49,16),(26,8),(17,9),(24,0),(80,0),(24,64)],[],[[]])
theorem p22_W : TabsP true p22_R p22_T p22_t := ⟨cutsGood p22_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p22_D10 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw83,pw176],[0,1,3,4,8,12,21,16,20,25,61,24,13,49,33,57,5,9,17,29,37,41,45,53,65,69,73,77,81,85,89,93,97,101,105,109],[65539,131075,4099,4099,262147,4099,524888,16912,1049104,2097200,16912,4202700,8421708,16778344,100665420,402661764,536872096,3221235844,4294968608,25769838852,34359739424])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p22_D9 : List StD := [
([pw0,pw1,pw2,pw4,pw88,pw10,pw83,pw176],[16,32,4,28,1,36,40,25,44,13,85,9,33,121,20,48,5,17,21,37,41,49,89,97,101,105,109,113,117,125,3],[65560,2072,536,2072,536,131096,536,134479876,4227,268435587,524419,1048739,4227,5,5,68,100,68,4,2105345,1057,4202499,16704,352,322,8389664,1660977154,67109922]),
([pw0,pw1,pw2,pw4,pw10,pw21,pw83,pw176],[20,40,52,1,56,4,25,13,49,117,57,85,137,24,5,9,17,33,41,89,109,125,129,133,141,145,3],[16396,32780,140,140,140,65548,140,577,131137,4195393,577,262161,577,290,33,1,50,34,8388611,4354,4114,524546,33,16777233,33555457,2066,69214210,1050640]),
([pw0,pw1,pw2,pw4,pw10,pw83,pw176,pw177],[24,40,4,60,1,64,25,13,49,85,9,33,77,3,20,5,17,37,41,73,97,149,153,157,161],[32792,1048,152,152,65560,152,1048,69,2113,131137,262177,2113,8259,262,6,38,5,5,4354,546,2097155,4354,1049120,4718593,8413186,16777249,546,4]),
([pw0,pw1,pw2,pw4,pw10,pw22,pw83,pw176],[20,40,68,1,72,25,76,13,45,77,85,21,33,61,81,93,117,3,16,80,84,5,9,17,37,41,53,65,69,97,109,121,125,165,169,173],[2097164,4194316,140,140,8589934604,8388620,140,65569,4129,16777249,4129,33554449,65569,2147486466,67125251,2370,17314086994,268435778,515,1,9234,426498,3,536870929,34359754753,9232,4296704000,1073742864]),
([pw0,pw1,pw2,pw4,pw10,pw83,pw176,pw178],[40,24,88,1,92,117,96,89,13,21,25,45,85,3,16,81,93,97,100,5,9,17,33,37,41,53,65,157,169,177,181,185],[524300,1048588,268,268,2097164,268,268,3617,4194467,8388643,16777267,1059,1059,2753,33555009,335544401,536936515,2625,57473,20625,131,2,135184,1073815554,134520832,2147483666,135184,1]),
([pw0,pw1,pw2,pw4,pw10,pw83,pw176,pw179],[108,24,104,1,112,116,120,3,13,77,117,25,53,61,97,145,40,5,9,17,21,33,37,41,49,65,69,85,89,125,153,173,189],[131084,262156,268,268,524300,268,141,3074,2099202,4194307,8388626,1027,1027,17826528,36929,33562704,1140850753,69697,2147484193,134225968,268435617,673,16401,32771,3,4294967313,16401,536870913])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p22_D8 : List StD := [
([pw0,pw1,pw2,pw4,pw88,pw10,pw83,pw176,pw179],[25,61,21,49,5,33,109,145,69,85,101,105,121,165,28,40,44,108,9,37,41,45,77,89,97,117,125,153,157,193,197,201,205,209,213,217,221,225,229,3],[1610612737,6442450948,25769803784,262160,8208,34359738386,8208,549755830288,68719476741,33,33554433,524289,1048579,33,33,137438953484,2097152,1156,518,260,260,4194304,4104,522,8388616,4104,1152,66,134219776,229376,16777218,274877909120,268435456,66,66,67108864]),
([pw180,pw0,pw1,pw2,pw4,pw10,pw83,pw176],[40,124,165,144,117,49,69,53,85,5,25,101,16,108,57,137,0,12,128,132,136,140,37,41,61,77,89,97,125,193,209,217,233,237],[66054,5137,193,36897,3950592,16908552,1,536870919,7,1073741831,518,2147483662,518,1041,4294967345,4194321,8388633,1041,193,193,329,193,33554465,32801,67108897,134220040,268462080,8589943048]),
([pw181,pw0,pw2,pw4,pw10,pw83,pw176],[40,148,152,25,29,85,9,49,77,5,165,156,21,37,69,89,97,101,109,117,157,209,217,241,245,249],[578,4121,393,8201,45,524297,578,2097155,1090,4194310,1090,401,8388625,53,16401,385,37,32897,65572,51513344,262180]),
([pw182,pw0,pw1,pw2,pw4,pw10,pw83,pw176],[40,160,164,5,53,25,69,85,49,165,108,37,73,77,105,0,12,136,140,168,172,41,61,89,97,117,157,161,193,209,217,233],[33290,2081,81,8449,1,4259972,1986560,268435467,11,536870923,522,1073741838,522,113,2147483937,2081,2097157,33554465,81,81,149,81,8449,133,8388865,16777348,67130368,134218884]),
([pw0,pw1,pw2,pw10,pw22,pw83,pw176,pw178],[5,25,45,16,180,81,108,89,40,176,85,165,21,93,117,37,77,97,84,96,1,9,17,41,53,61,69,169,185,253,257,261,265,269,3],[537919491,1075838981,2147485729,2689,4194817,2561,2561,20486,4295000098,32906,8388634,16394,16394,16777508,528516,134219028,67117316,69892,8,132144,8589942880,17179934816,33555600,270528,64,268435536,132112,8]),
([pw0,pw1,pw2,pw4,pw10,pw22,pw83,pw176,pw183],[25,45,61,108,5,21,93,13,37,85,84,77,105,68,184,41,53,65,97,101,117,165,177,185,193,197,217,233,273,277],[50331649,805306370,144,144,2097168,67108884,144,8216,35,134219777,257,257,32773,1048577,257,34,65538,34,131078,4194370,34,2056,8,516,4168,8,524288,262148,4160,16384,516,1032,8,8388676,516,1024]),
([pw0,pw1,pw2,pw4,pw10,pw83,pw176,pw183],[108,192,5,25,45,188,77,61,265,285,116,13,21,289,117,4,16,40,84,1,9,17,33,81,93,97,121,145,153,157,185,253,257,281,3],[2148007948,4296015892,2148,2084,2097188,2084,37,20504,8594128968,8388873,650,16785417,82952,67113040,134218001,658,268443665,167952,1281,706,1121,1,33554435,8451,17716740097,1073741827,642,262144]),
([pw184,pw0,pw1,pw2,pw4,pw10,pw83,pw176],[200,84,196,204,165,25,77,85,40,5,81,37,117,145,0,4,188,9,41,45,49,61,69,73,89,97,109,121,125,157,193,217,233,293],[16916,2337,33026,1048899,536870915,138,65538,1073741845,131092,8589934613,532,2147483676,532,4129,4294967393,2081,262185,4129,134217793,9218,2097288,281542656,1031,137,16777281,33554442,9218,67109000]),
([pw0,pw1,pw2,pw4,pw10,pw83,pw178,pw179],[108,116,5,25,45,212,89,208,216,13,21,117,53,61,85,97,153,40,1,9,17,33,37,41,65,145,157,181,253,257,297,3],[268697612,537395220,708,644,1048708,644,1073741957,3096,2097226,4194315,8388650,2058,2059,1362,33558801,16785712,66832,135441,134217795,16482,1,67,32801,2147549187,67108865,24608,32801,3]),
([pw0,pw1,pw2,pw4,pw10,pw83,pw176,pw178,pw183],[25,45,61,108,5,21,81,85,37,93,101,117,165,88,200,41,53,65,89,97,105,157,177,185,193,197,217,273,277,293,301,305,309,313,3],[50331649,402653186,1610612752,2147483728,67108884,4112,4112,8216,35,12884901889,257,32773,2049,2049,257,34,65538,131078,4194818,34,34,1096,132,262152,8,8,524356,1088,17179869192,2097152,8389124,132,132,1048576,16384,8]),
([pw185,pw0,pw1,pw2,pw4,pw10,pw83,pw176,pw178],[108,5,25,45,61,89,157,85,93,117,165,21,3,16,220,41,81,105,177,185,309,317,321,325],[1026,516,2056,16417,65536,144,8449,1,7,11,35,1026,19,1026,1026,516,1048612,2097220,32788,516,516,2056,4194376,152,262408,2056,4192,176,33,1,8388673,4416,4097,524545,144,131072]),
([pw185,pw0,pw1,pw2,pw4,pw10,pw83,pw176],[184,224,228,5,25,45,61,77,89,85,93,117,165,16,108,153,157,0,4,12,40,140,188,9,21,37,41,53,57,69,97,185,193,217,233,293,3],[135178,10257,18087968,8577,68723671040,524868,2098177,4294967307,8388618,34359738379,4106,8589934606,4106,2065,17179869457,33554449,67108885,2065,385,402718752,612,536904736,385,517,131,1073741892,115712,2147500100]),
([pw186,pw1,pw2,pw4,pw10,pw83,pw176],[108,236,240,1,232,244,13,21,341,25,33,61,333,5,9,17,29,41,45,49,65,85,297,305,329,337,345,349,353,3],[8201,16393,73,73,32777,73,66194,1538,16777219,131078,1027,537657520,33558545,1050772,67109137,8392737,2099236,4194593,134217733,263,268435461])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p22_D7 : List StD := [
([pw186,pw1,pw2,pw4,pw88,pw10,pw83,pw176],[5,25,61,337,121,21,341,9,33,49,85,109,333,345,41,45,77,81,117,165,221,225,229,297,329,349,357,361],[67108867,129,529,129,131081,134217733,524289,1048610,258,262146,16777226,16390,258,2097200,32768,4104,1060,8288,65536,528,1044,8388688,4104,2052,8256,33554444,4194376,2052]),
([pw185,pw0,pw1,pw2,pw22,pw83,pw176,pw178],[5,21,25,85,81,157,45,61,89,93,117,165,41,105,177,181,185,193,217,273,305,317,365,369],[1048593,4194324,82,304,152,33296,8388608,131077,524291,289,262153,2561,2049,70,2097188,4108,1028,1028,66,138,16898,66,168,288,288,66056,136,8192]),
([pw185,pw0,pw1,pw2,pw4,pw83,pw176,pw183],[5,21,25,85,81,77,93,45,61,117,0,224,41,89,165,177,185,193,217,229,233,273,293,305,337,365,369,373,377],[8388625,33554452,146,67108912,280,524368,1024,131077,2097155,4194337,262153,16449,16779265,134,1048612,4108,516,516,130,266,32834,130,296,8288,134217728,65608,264,268435456]),
([pw185,pw0,pw1,pw2,pw4,pw83,pw178,pw179],[5,25,85,45,157,89,61,117,21,93,181,165,41,77,193,217,229,273,289,293,309,321,325,381],[2049,130,264,8389664,1092,65536,1552,16387,131081,524321,32773,2049,262161,130,1048610,4102,130,130,264,76,264,2097176,100,8192,560,68,4194324,528])]
def p22_D6 : List StD := []
theorem p22_I6 : LevelN true p22_T 6 p22_D6 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p22_C7x0 : levelOK true p22_T p22_t 6 (p22_D6.map Prod.fst) ((p22_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p22_I7 : LevelN true p22_T 7 p22_D7 := levelStep p22_B p22_W p22_I6 (chunks 32 p22_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p22_C7x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p22_C8x0 : levelOK true p22_T p22_t 7 (p22_D7.map Prod.fst) ((p22_D8.drop (0*32)).take 32) = true := by decide +kernel
theorem p22_I8 : LevelN true p22_T 8 p22_D8 := levelStep p22_B p22_W p22_I7 (chunks 32 p22_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p22_C8x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p22_C9x0 : levelOK true p22_T p22_t 8 (p22_D8.map Prod.fst) ((p22_D9.drop (0*32)).take 32) = true := by decide +kernel
theorem p22_I9 : LevelN true p22_T 9 p22_D9 := levelStep p22_B p22_W p22_I8 (chunks 32 p22_D9 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p22_C9x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p22_C10x0 : levelOK true p22_T p22_t 9 (p22_D9.map Prod.fst) ((p22_D10.drop (0*32)).take 32) = true := by decide +kernel
theorem p22_I10 : LevelN true p22_T 10 p22_D10 := levelStep p22_B p22_W p22_I9 (chunks 32 p22_D10 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p22_C10x0
  ))
theorem p22_L : LowN true p22_R p22_T 11 := lowSearch p22_B p22_I10 (by decide +kernel)
def p23_T : Nat := 0xfffefefeffeeeeeafffefefeffeeeeeafffefefeffeeeeeafffefefeffeeeeea
def p23_R : List Nat := [0, 1, 2, 3, 4, 5]
def p23_E : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6),(3,2,10),(4,2,18),(5,2,34)]
theorem p23_B : baseOK p23_T p23_R p23_E = true := by decide +kernel
def p23_Z : List SliceD := [(pw84,8,[1, 2, 3, 4, 5])]
theorem p23_Y : ∀ s ∈ p23_Z, SliceN true p23_R p23_T s := by
  unfold p23_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p23_B p3_B p3_L (by decide +kernel),by simp⟩
def p23_C : List (Nat × List Nat) := [(0,[])]
def p23_t : Tabs := (p23_C.map (mkCut true p23_Z),[],[],[[]])
theorem p23_W : TabsP true p23_R p23_T p23_t := ⟨cutsGood p23_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p23_D8 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw83],[0],[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])]
def p23_D7 : List StD := []
theorem p23_I7 : LevelN true p23_T 7 p23_D7 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p23_C8x0 : levelOK true p23_T p23_t 7 (p23_D7.map Prod.fst) ((p23_D8.drop (0*32)).take 32) = true := by decide +kernel
theorem p23_I8 : LevelN true p23_T 8 p23_D8 := levelStep p23_B p23_W p23_I7 (chunks 32 p23_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p23_C8x0
  ))
theorem p23_L : LowN true p23_R p23_T 9 := lowSearch p23_B p23_I8 (by decide +kernel)
def p24_T : Nat := 0xfffffffffffffffffffffffffffeeac0fffffffffffffffffffffffffffeeac0
def p24_R : List Nat := [0, 1, 2, 3, 4, 5, 6]
def p24_E : List (Nat × Nat × Nat) := [(0,8,9),(1,4,6),(2,2,6),(3,1,9),(4,1,17),(5,0,32),(6,0,64)]
theorem p24_B : baseOK p24_T p24_R p24_E = true := by decide +kernel
def p24_Z : List SliceD := [(pw91,9,[6, 4, 2, 3, 0, 1])]
theorem p24_Y : ∀ s ∈ p24_Z, SliceN true p24_R p24_T s := by
  unfold p24_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p24_B p23_B p23_L (by decide +kernel),by simp⟩
def p24_C : List (Nat × List Nat) := [(0,[])]
def p24_t : Tabs := (p24_C.map (mkCut true p24_Z),[],[],[[]])
theorem p24_W : TabsP true p24_R p24_T p24_t := ⟨cutsGood p24_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p24_D9 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw83,pw176],[0],[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])]
def p24_D8 : List StD := []
theorem p24_I8 : LevelN true p24_T 8 p24_D8 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p24_C9x0 : levelOK true p24_T p24_t 8 (p24_D8.map Prod.fst) ((p24_D9.drop (0*32)).take 32) = true := by decide +kernel
theorem p24_I9 : LevelN true p24_T 9 p24_D9 := levelStep p24_B p24_W p24_I8 (chunks 32 p24_D9 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p24_C9x0
  ))
theorem p24_L : LowN true p24_R p24_T 10 := lowSearch p24_B p24_I9 (by decide +kernel)
def p25_T : Nat := 0xfffffffffffefffcffffeaeaffeac0c0fffffffffffefffcffffeaeaffeac0c0
def p25_R : List Nat := [0, 1, 2, 3, 4, 5, 6]
def p25_E : List (Nat × Nat × Nat) := [(0,16,17),(1,4,6),(2,2,6),(3,16,24),(4,1,17),(5,1,33),(6,2,66)]
theorem p25_B : baseOK p25_T p25_R p25_E = true := by decide +kernel
def p25_Z : List SliceD := [(pw3,10,[5, 4, 6, 1, 2, 0])]
theorem p25_Y : ∀ s ∈ p25_Z, SliceN true p25_R p25_T s := by
  unfold p25_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p25_B p12_B p12_L (by decide +kernel),by simp⟩
def p25_C : List (Nat × List Nat) := [(0,[])]
def p25_t : Tabs := (p25_C.map (mkCut true p25_Z),[],[],[[]])
theorem p25_W : TabsP true p25_R p25_T p25_t := ⟨cutsGood p25_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p25_D10 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw83,pw176],[0],[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])]
def p25_D9 : List StD := []
theorem p25_I9 : LevelN true p25_T 9 p25_D9 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p25_C10x0 : levelOK true p25_T p25_t 9 (p25_D9.map Prod.fst) ((p25_D10.drop (0*32)).take 32) = true := by decide +kernel
theorem p25_I10 : LevelN true p25_T 10 p25_D10 := levelStep p25_B p25_W p25_I9 (chunks 32 p25_D10 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p25_C10x0
  ))
theorem p25_L : LowN true p25_R p25_T 11 := lowSearch p25_B p25_I10 (by decide +kernel)
def p26_T : Nat := 0xfeeefaeafeecfae0feeefaeafeecfae0feeefaeafeecfae0feeefaeafeecfae0
def p26_R : List Nat := [0, 1, 2, 3, 4, 5]
def p26_E : List (Nat × Nat × Nat) := [(0,4,5),(1,4,6),(2,1,5),(3,1,9),(4,2,18),(5,1,33)]
theorem p26_B : baseOK p26_T p26_R p26_E = true := by decide +kernel
def p26_Z : List SliceD := [(pw91,7,[1, 2, 0, 3, 4])]
theorem p26_Y : ∀ s ∈ p26_Z, SliceN true p26_R p26_T s := by
  unfold p26_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p26_B p7_B p7_L (by decide +kernel),by simp⟩
def p26_C : List (Nat × List Nat) := [(0,[])]
def p26_t : Tabs := (p26_C.map (mkCut true p26_Z),[],[],[[]])
theorem p26_W : TabsP true p26_R p26_T p26_t := ⟨cutsGood p26_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p26_D7 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw83],[0],[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])]
def p26_D6 : List StD := []
theorem p26_I6 : LevelN true p26_T 6 p26_D6 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p26_C7x0 : levelOK true p26_T p26_t 6 (p26_D6.map Prod.fst) ((p26_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p26_I7 : LevelN true p26_T 7 p26_D7 := levelStep p26_B p26_W p26_I6 (chunks 32 p26_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p26_C7x0
  ))
theorem p26_L : LowN true p26_R p26_T 8 := lowSearch p26_B p26_I7 (by decide +kernel)
def p27_T : Nat := 0xfffffffffffffff0ffffecececa0eca0fffffffffffffff0ffffecececa0eca0
def p27_R : List Nat := [0, 1, 2, 3, 4, 5, 6]
def p27_E : List (Nat × Nat × Nat) := [(0,4,5),(1,8,10),(2,1,5),(3,2,10),(4,32,48),(5,2,34),(6,4,68)]
theorem p27_B : baseOK p27_T p27_R p27_E = true := by decide +kernel
def p27_Z : List SliceD := [(pw84,8,[6, 5, 1, 3, 4, 2])]
theorem p27_Y : ∀ s ∈ p27_Z, SliceN true p27_R p27_T s := by
  unfold p27_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p27_B p19_B p19_L (by decide +kernel),by simp⟩
def p27_C : List (Nat × List Nat) := [(0,[])]
def p27_t : Tabs := (p27_C.map (mkCut true p27_Z),[],[],[[]])
theorem p27_W : TabsP true p27_R p27_T p27_t := ⟨cutsGood p27_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p27_D8 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw83,pw176],[0],[1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1])]
def p27_D7 : List StD := []
theorem p27_I7 : LevelN true p27_T 7 p27_D7 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p27_C8x0 : levelOK true p27_T p27_t 7 (p27_D7.map Prod.fst) ((p27_D8.drop (0*32)).take 32) = true := by decide +kernel
theorem p27_I8 : LevelN true p27_T 8 p27_D8 := levelStep p27_B p27_W p27_I7 (chunks 32 p27_D8 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p27_C8x0
  ))
theorem p27_L : LowN true p27_R p27_T 9 := lowSearch p27_B p27_I8 (by decide +kernel)
def p28_T : Nat := 0xfffffffefffefefefffffffefffefefefffffffefffefefefffffffefffefefe
def p28_R : List Nat := [0, 1, 2, 3, 4, 5]
def p28_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,0,4),(3,16,24),(4,8,24),(5,8,40)]
theorem p28_B : baseOK p28_T p28_R p28_E = true := by decide +kernel
def p28_Z : List SliceD := [(pw84,6,[1, 2, 3, 4, 5])]
theorem p28_Y : ∀ s ∈ p28_Z, SliceN true p28_R p28_T s := by
  unfold p28_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p28_B p9_B p9_L (by decide +kernel),by simp⟩
def p28_C : List (Nat × List Nat) := [(0,[])]
def p28_t : Tabs := (p28_C.map (mkCut true p28_Z),[(1,0),(2,0)],[],[[]])
theorem p28_W : TabsP true p28_R p28_T p28_t := ⟨cutsGood p28_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p28_D6 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw83],[0,1,5],[7,3,3,3,3,5,5,5,5,1,1,1,1,1,1])]
def p28_D5 : List StD := []
theorem p28_I5 : LevelN true p28_T 5 p28_D5 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p28_C6x0 : levelOK true p28_T p28_t 5 (p28_D5.map Prod.fst) ((p28_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p28_I6 : LevelN true p28_T 6 p28_D6 := levelStep p28_B p28_W p28_I5 (chunks 32 p28_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p28_C6x0
  ))
theorem p28_L : LowN true p28_R p28_T 7 := lowSearch p28_B p28_I6 (by decide +kernel)
def p29_T : Nat := 0xffffffffffffffffffffffffffffffe8ffffffffffffffffffffffffffffffe8
def p29_R : List Nat := [0, 1, 2, 3, 4, 5, 6]
def p29_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,0,8),(4,0,16),(5,0,32),(6,0,64)]
theorem p29_B : baseOK p29_T p29_R p29_E = true := by decide +kernel
def p29_Z : List SliceD := [(pw3,7,[4, 5, 6, 0, 1, 2])]
theorem p29_Y : ∀ s ∈ p29_Z, SliceN true p29_R p29_T s := by
  unfold p29_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p29_B p28_B p28_L (by decide +kernel),by simp⟩
def p29_C : List (Nat × List Nat) := [(0,[])]
def p29_t : Tabs := (p29_C.map (mkCut true p29_Z),[(5,4),(6,4),(3,2),(3,1),(6,2),(5,1),(8,0)],[],[[]])
theorem p29_W : TabsP true p29_R p29_T p29_t := ⟨cutsGood p29_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p29_D7 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw83,pw176],[0,1,5,17,25,9,13,21],[102,170,19,3,3,3,204,21,5,5,5,25,9,9,9,17,17,17,1,1,1])]
def p29_D6 : List StD := []
theorem p29_I6 : LevelN true p29_T 6 p29_D6 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p29_C7x0 : levelOK true p29_T p29_t 6 (p29_D6.map Prod.fst) ((p29_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p29_I7 : LevelN true p29_T 7 p29_D7 := levelStep p29_B p29_W p29_I6 (chunks 32 p29_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p29_C7x0
  ))
theorem p29_L : LowN true p29_R p29_T 8 := lowSearch p29_B p29_I7 (by decide +kernel)
def p30_T : Nat := 0xfeeefaeafeeefaeafeeefaeafeeefaeafeeefaeafeeefaeafeeefaeafeeefaea
def p30_R : List Nat := [0, 1, 2, 3, 4]
def p30_E : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6),(3,4,12),(4,2,18)]
theorem p30_B : baseOK p30_T p30_R p30_E = true := by decide +kernel
def p30_Z : List SliceD := []
theorem p30_Y : ∀ s ∈ p30_Z, SliceN true p30_R p30_T s := by
  intro s h
  cases h
def p30_C : List (Nat × List Nat) := []
def p30_t : Tabs := (p30_C.map (mkCut true p30_Z),[(1,0),(1,2),(3,0),(1,4),(5,0),(1,8),(9,0),(1,16),(17,0),(12,8),(6,2),(6,4),(18,24),(12,4),(18,2),(18,0),(12,24),(18,10)],[],[[]])
theorem p30_W : TabsP true p30_R p30_T p30_t := ⟨cutsGood p30_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p30_D4 : List StD := [
([pw0,pw1,pw2,pw4,pw10],[1,37,57,41,45,53,5,9,13,17,21,25,29,33,49,61,65,69],[193,769,3073,12289,10,16432,32788,10,65542,131108])]
def p30_D3 : List StD := []
theorem p30_I3 : LevelN true p30_T 3 p30_D3 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p30_C4x0 : levelOK true p30_T p30_t 3 (p30_D3.map Prod.fst) ((p30_D4.drop (0*32)).take 32) = true := by decide +kernel
theorem p30_I4 : LevelN true p30_T 4 p30_D4 := levelStep p30_B p30_W p30_I3 (chunks 32 p30_D4 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p30_C4x0
  ))
theorem p30_L : LowN true p30_R p30_T 5 := lowSearch p30_B p30_I4 (by decide +kernel)
def p31_T : Nat := 0xfeeefaaafcecf8a8feeefaaafcecf8a8feeefaaafcecf8a8feeefaaafcecf8a8
def p31_R : List Nat := [0, 1, 2, 3, 4, 5]
def p31_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,4,12),(4,2,18),(5,1,33)]
theorem p31_B : baseOK p31_T p31_R p31_E = true := by decide +kernel
def p31_Z : List SliceD := [(pw4,5,[2, 1, 0, 5, 4]),(pw3,5,[0, 1, 4, 2, 5]),(pw10,5,[1, 0, 2, 3, 5]),(pw7,5,[0, 2, 3, 1, 5]),(pw91,5,[1, 2, 0, 3, 4]),(pw8,4,[0, 2, 3, 5]),(pw9,4,[0, 1, 4, 5])]
theorem p31_Y : ∀ s ∈ p31_Z, SliceN true p31_R p31_T s := by
  unfold p31_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=8) p31_B p30_B p30_L (by decide +kernel),mkSlice (w:=0) p31_B p17_B p17_L (by decide +kernel),mkSlice (w:=16) p31_B p30_B p30_L (by decide +kernel),mkSlice (w:=0) p31_B p17_B p17_L (by decide +kernel),mkSlice (w:=0) p31_B p20_B p20_L (by decide +kernel),mkSlice (w:=0) p31_B p5_B p5_L (by decide +kernel),mkSlice (w:=0) p31_B p5_B p5_L (by decide +kernel),by simp⟩
def p31_C : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[])]
def p31_t : Tabs := (p31_C.map (mkCut true p31_Z),[(5,4),(18,16),(3,2),(3,1),(12,8),(5,1),(12,4),(11,10),(18,2),(21,20),(33,1),(33,0),(22,20),(14,10),(18,48),(12,40),(41,1),(49,1),(33,8),(33,16),(12,10),(3,9),(5,17),(18,10)],[],[[]])
theorem p31_W : TabsP true p31_R p31_T p31_t := ⟨cutsGood p31_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p31_D6 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw83],[0,4,1,25,8,12,5,17,33,16,9,13,21,20,24,29,37,41,45,49,53,57,61,3],[3140,5252,32783,65844,8782340,1573056,75,2352,2105920,4107,432,4211328,11,11,304])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p31_D5 : List StD := [
([pw103,pw0,pw1,pw2,pw4,pw10],[5,17,25,33,13,21,41,45,9,65,69,73,77,81,85,89,93],[256,17,34,580,1096,17,34,2180,4232,8195,16389,17,34,32778,65548])]
def p31_D4 : List StD := []
theorem p31_I4 : LevelN true p31_T 4 p31_D4 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p31_C5x0 : levelOK true p31_T p31_t 4 (p31_D4.map Prod.fst) ((p31_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p31_I5 : LevelN true p31_T 5 p31_D5 := levelStep p31_B p31_W p31_I4 (chunks 32 p31_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p31_C5x0
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p31_C6x0 : levelOK true p31_T p31_t 5 (p31_D5.map Prod.fst) ((p31_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p31_I6 : LevelN true p31_T 6 p31_D6 := levelStep p31_B p31_W p31_I5 (chunks 32 p31_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p31_C6x0
  ))
theorem p31_L : LowN true p31_R p31_T 7 := lowSearch p31_B p31_I6 (by decide +kernel)
def p32_T : Nat := 0xfffffffffffffffffffffffffffffec0fffffffffffffffffffffffffffffec0
def p32_R : List Nat := [0, 1, 2, 3, 4, 5, 6]
def p32_E : List (Nat × Nat × Nat) := [(0,8,9),(1,4,6),(2,2,6),(3,1,9),(4,0,16),(5,0,32),(6,0,64)]
theorem p32_B : baseOK p32_T p32_R p32_E = true := by decide +kernel
def p32_Z : List SliceD := [(pw84,7,[4, 5, 6, 1, 2, 3])]
theorem p32_Y : ∀ s ∈ p32_Z, SliceN true p32_R p32_T s := by
  unfold p32_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p32_B p28_B p28_L (by decide +kernel),by simp⟩
def p32_C : List (Nat × List Nat) := [(0,[])]
def p32_t : Tabs := (p32_C.map (mkCut true p32_Z),[(9,8),(6,4)],[],[[]])
theorem p32_W : TabsP true p32_R p32_T p32_t := ⟨cutsGood p32_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p32_D7 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw83,pw176],[0,1,5],[7,3,1,3,3,3,1,5,5,5,5,1,1,1,1,1,1,1,1,1,1])]
def p32_D6 : List StD := []
theorem p32_I6 : LevelN true p32_T 6 p32_D6 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p32_C7x0 : levelOK true p32_T p32_t 6 (p32_D6.map Prod.fst) ((p32_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p32_I7 : LevelN true p32_T 7 p32_D7 := levelStep p32_B p32_W p32_I6 (chunks 32 p32_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p32_C7x0
  ))
theorem p32_L : LowN true p32_R p32_T 8 := lowSearch p32_B p32_I7 (by decide +kernel)
def p33_T : Nat := 0xfeeefeeafeeefeeafeeefeeafeeefeeafeeefeeafeeefeeafeeefeeafeeefeea
def p33_R : List Nat := [0, 1, 2, 3, 4]
def p33_E : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6),(3,2,10),(4,2,18)]
theorem p33_B : baseOK p33_T p33_R p33_E = true := by decide +kernel
def p33_Z : List SliceD := [(pw84,5,[1, 2, 3, 4])]
theorem p33_Y : ∀ s ∈ p33_Z, SliceN true p33_R p33_T s := by
  unfold p33_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p33_B p2_B p2_L (by decide +kernel),by simp⟩
def p33_C : List (Nat × List Nat) := [(0,[])]
def p33_t : Tabs := (p33_C.map (mkCut true p33_Z),[(1,0),(6,4),(3,2)],[],[[]])
theorem p33_W : TabsP true p33_R p33_T p33_t := ⟨cutsGood p33_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p33_D5 : List StD := [
([pw0,pw1,pw2,pw4,pw10],[0,1,5,9],[15,3,3,3,1,5,5,1,1,1])]
def p33_D4 : List StD := []
theorem p33_I4 : LevelN true p33_T 4 p33_D4 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p33_C5x0 : levelOK true p33_T p33_t 4 (p33_D4.map Prod.fst) ((p33_D5.drop (0*32)).take 32) = true := by decide +kernel
theorem p33_I5 : LevelN true p33_T 5 p33_D5 := levelStep p33_B p33_W p33_I4 (chunks 32 p33_D5 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p33_C5x0
  ))
theorem p33_L : LowN true p33_R p33_T 6 := lowSearch p33_B p33_I5 (by decide +kernel)
def p34_T : Nat := 0xfffefefefffefeeefffefefefffefeeefffefefefffefeeefffefefefffefeee
def p34_R : List Nat := [0, 1, 2, 3, 4, 5]
def p34_E : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,8,12),(3,4,12),(4,4,20),(5,4,36)]
theorem p34_B : baseOK p34_T p34_R p34_E = true := by decide +kernel
def p34_Z : List SliceD := [(pw84,6,[1, 2, 3, 4, 5])]
theorem p34_Y : ∀ s ∈ p34_Z, SliceN true p34_R p34_T s := by
  unfold p34_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p34_B p33_B p33_L (by decide +kernel),by simp⟩
def p34_C : List (Nat × List Nat) := [(0,[])]
def p34_t : Tabs := (p34_C.map (mkCut true p34_Z),[(1,0),(2,0)],[],[[]])
theorem p34_W : TabsP true p34_R p34_T p34_t := ⟨cutsGood p34_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p34_D6 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw83],[0,1,5],[7,3,3,3,3,5,5,5,5,1,1,1,1,1,1])]
def p34_D5 : List StD := []
theorem p34_I5 : LevelN true p34_T 5 p34_D5 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p34_C6x0 : levelOK true p34_T p34_t 5 (p34_D5.map Prod.fst) ((p34_D6.drop (0*32)).take 32) = true := by decide +kernel
theorem p34_I6 : LevelN true p34_T 6 p34_D6 := levelStep p34_B p34_W p34_I5 (chunks 32 p34_D6 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p34_C6x0
  ))
theorem p34_L : LowN true p34_R p34_T 7 := lowSearch p34_B p34_I6 (by decide +kernel)
def p35_T : Nat := 0xfffffffffffffffffffffffffffafc88fffffffffffffffffffffffffffafc88
def p35_R : List Nat := [0, 1, 2, 3, 4, 5, 6]
def p35_E : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,8,12),(3,2,10),(4,1,17),(5,0,32),(6,0,64)]
theorem p35_B : baseOK p35_T p35_R p35_E = true := by decide +kernel
def p35_Z : List SliceD := [(pw84,7,[5, 6, 3, 4, 2, 1])]
theorem p35_Y : ∀ s ∈ p35_Z, SliceN true p35_R p35_T s := by
  unfold p35_Z
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) p35_B p34_B p34_L (by decide +kernel),by simp⟩
def p35_C : List (Nat × List Nat) := [(0,[])]
def p35_t : Tabs := (p35_C.map (mkCut true p35_Z),[(17,16),(10,8),(3,2),(3,1),(12,8),(7,6),(13,9),(10,2)],[],[[]])
theorem p35_W : TabsP true p35_R p35_T p35_t := ⟨cutsGood p35_Y (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def p35_D7 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw83,pw176],[0,1,5,17,29,9,13,21,25],[102,394,19,33,3,3,13,65,5,5,5,1,9,9,9,17,17,17,1,1,1])]
def p35_D6 : List StD := []
theorem p35_I6 : LevelN true p35_T 6 p35_D6 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem p35_C7x0 : levelOK true p35_T p35_t 6 (p35_D6.map Prod.fst) ((p35_D7.drop (0*32)).take 32) = true := by decide +kernel
theorem p35_I7 : LevelN true p35_T 7 p35_D7 := levelStep p35_B p35_W p35_I6 (chunks 32 p35_D7 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact p35_C7x0
  ))
theorem p35_L : LowN true p35_R p35_T 8 := lowSearch p35_B p35_I7 (by decide +kernel)
def ptopT : Nat := 0xfffffffffffffffefffffffffffffefcfffefffefffefffefefefafaeeccaa00
def ptopR : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]
def ptopE : List (Nat × Nat × Nat) := [(0,8,9),(1,16,18),(2,32,36),(3,1,9),(4,2,18),(5,1,33),(6,1,65),(7,2,130)]
theorem ptopB : baseOK ptopT ptopR ptopE = true := by decide +kernel
def ptopZ : List SliceD := [(pw187,9,[7, 2, 1, 6, 4, 5]),(pw8,9,[0, 6, 2, 5, 7, 3]),(pw133,10,[1, 4, 6, 0, 3, 7]),(pw7,11,[3, 1, 7, 5, 0, 2, 6]),(pw188,8,[7, 2, 4, 1, 5]),(pw4,10,[1, 2, 5, 4, 7, 0, 6]),(pw91,11,[4, 0, 3, 2, 7, 1, 6]),(pw189,8,[7, 6, 2, 5, 3, 4]),(pw190,9,[4, 5, 1, 2, 3, 0, 6]),(pw191,8,[0, 3, 6, 1, 2, 4, 5]),(pw192,7,[6, 2, 1, 4, 5, 3]),(pw171,8,[7, 0, 5, 2, 3, 4]),(pw193,6,[0, 6, 2, 5, 3]),(pw194,7,[2, 4, 5, 0, 3, 6]),(pw0,8,[2, 1, 4, 7, 3, 5, 6]),(pw195,7,[1, 2, 5, 3, 0, 6]),(pw10,8,[2, 5, 3, 0, 6, 1, 7]),(pw196,9,[0, 6, 7, 1, 5, 3]),(pw14,7,[3, 5, 6, 1, 4, 7]),(pw96,7,[1, 7, 0, 6, 3, 5])]
theorem ptopY : ∀ s ∈ ptopZ, SliceN true ptopR ptopT s := by
  unfold ptopZ
  simp only [List.forall_mem_cons]
  exact ⟨mkSlice (w:=0) ptopB p4_B p4_L (by decide +kernel),mkSlice (w:=0) ptopB p10_B p10_L (by decide +kernel),mkSlice (w:=0) ptopB p12_B p12_L (by decide +kernel),mkSlice (w:=0) ptopB p22_B p22_L (by decide +kernel),mkSlice (w:=0) ptopB p3_B p3_L (by decide +kernel),mkSlice (w:=8) ptopB p24_B p24_L (by decide +kernel),mkSlice (w:=0) ptopB p25_B p25_L (by decide +kernel),mkSlice (w:=0) ptopB p26_B p26_L (by decide +kernel),mkSlice (w:=0) ptopB p27_B p27_L (by decide +kernel),mkSlice (w:=128) ptopB p29_B p29_L (by decide +kernel),mkSlice (w:=0) ptopB p31_B p31_L (by decide +kernel),mkSlice (w:=0) ptopB p26_B p26_L (by decide +kernel),mkSlice (w:=0) ptopB p8_B p8_L (by decide +kernel),mkSlice (w:=128) ptopB p28_B p28_L (by decide +kernel),mkSlice (w:=1) ptopB p32_B p32_L (by decide +kernel),mkSlice (w:=128) ptopB p28_B p28_L (by decide +kernel),mkSlice (w:=16) ptopB p35_B p35_L (by decide +kernel),mkSlice (w:=0) ptopB p21_B p21_L (by decide +kernel),mkSlice (w:=1) ptopB p28_B p28_L (by decide +kernel),mkSlice (w:=16) ptopB p34_B p34_L (by decide +kernel),by simp⟩
def ptopC : List (Nat × List Nat) := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[645]),(2,[385]),(7,[]),(8,[]),(2,[653]),(3,[521]),(1,[513]),(9,[]),(10,[]),(2,[655]),(3,[522]),(2,[257]),(3,[773]),(11,[]),(2,[641]),(4,[385]),(12,[]),(3,[261]),(2,[643]),(3,[263]),(4,[386]),(1,[517]),(2,[649]),(13,[]),(3,[777]),(2,[651]),(3,[778]),(2,[385,653]),(14,[]),(2,[385,665]),(2,[653,26]),(3,[521,158]),(1,[515]),(2,[655,25]),(2,[257,649]),(3,[773,777]),(8,[777]),(2,[257,665]),(8,[650]),(2,[641,410]),(3,[261,542]),(4,[385,651]),(2,[641,775]),(4,[385,278]),(15,[]),(16,[]),(2,[641,154]),(8,[259]),(2,[641,649]),(3,[261,777]),(3,[261,778]),(1,[516]),(1,[519]),(2,[651,641]),(8,[778]),(2,[641,282]),(3,[261,798]),(2,[643,409]),(2,[643,281]),(3,[777,261]),(2,[649,643]),(4,[384]),(3,[263,777]),(2,[649,26]),(2,[651,25]),(3,[261,541]),(17,[257,409]),(18,[]),(8,[649,30]),(3,[261,797]),(17,[261,409]),(19,[]),(8,[777,30])]
def ptopt : Tabs := (ptopC.map (mkCut true ptopZ),[(9,8),(11,10),(19,17),(133,129),(13,8),(33,32),(72,64),(9,1),(19,3),(18,2),(33,1),(65,64),(65,1),(137,136),(131,3),(38,34),(11,3),(144,128),(35,3),(66,64),(66,2),(130,128),(9,5),(18,6),(68,64),(9,17),(36,12),(137,129),(33,17),(208,192),(224,192),(193,129),(208,80),(15,14),(35,34),(18,3),(130,3),(23,21),(9,3),(131,129),(33,3),(65,3),(36,32),(36,4),(68,4),(130,2),(132,128),(65,17),(66,34),(160,128),(132,129),(193,192),(18,16),(36,0),(65,5),(131,7),(9,129),(33,129),(65,129),(200,192),(200,136),(9,12),(9,0),(133,5),(13,12),(25,24),(194,192),(66,6),(66,10),(138,136),(44,40),(26,10),(44,12),(72,8),(138,10),(132,4),(11,8),(18,20),(26,24),(22,16),(52,48),(25,17),(49,17),(144,192),(160,192),(65,0),(130,129),(11,2),(19,21),(11,14),(145,129),(130,6),(130,192),(82,64),(38,6),(133,21),(22,6),(50,34),(132,6),(18,0),(144,0),(19,1),(18,4),(26,8),(18,32),(208,64),(66,192),(134,6),(130,10),(162,34),(68,12),(72,40),(130,34),(22,20),(50,48),(13,5),(33,5),(9,10),(25,8),(22,4),(50,32),(104,96),(98,34)],[],[[]])
theorem ptopW : TabsP true ptopR ptopT ptopt := ⟨cutsGood ptopY (by decide +kernel),by decide +kernel,by decide +kernel,by decide +kernel⟩
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD12 : List StD := [
([pw0,pw1,pw2,pw4,pw10,pw83,pw176,pw191],[0,8,4,12,1,20,9,13,25,33,41,3,16,61,21,29,49,57,69,121,5,17,37,45,53,65,73,77,81,85,89,93,97,101,105,109,113,117,125,129],[1050709,2097299,49425,4194841,17427,8458257,16910353,8390,33554789,262668,67109958,402659396,537004100,1073741987,2147483662,8322,4294967426,8322,8589935405,17179870243,37153,34359738657,68719476750,137438953996,262668,525314,525314,824633792512])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD11 : List StD := [
([pw0,pw1,pw11,pw2,pw4,pw10,pw83,pw176,pw191],[0,4,16,24,28,133,29,49,61,149,25,37,41,69,137,157,177,3,32,36,5,9,89,93,101,105,109,113,125,141,145,153,161,165,169,173,181,185,189,193,197],[3,3,1048609,16417,536870915,16417,133,1073872929,1,2097666,2147483651,33282,4294967306,8589934598,33282,17179869456,1089,10242,34359742472,65668,68720394240,4194321,8388626,280,65556,137438953744,16777219,33554441,1093,67108929,134217738,274877906950,10242,549755813900,1099511631880,268435588]),
([pw0,pw1,pw2,pw4,pw10,pw83,pw176,pw191,pw197],[0,40,44,52,16,36,25,41,9,33,61,48,56,29,53,57,81,49,69,3,37,65,73,85,89,93,101,105,113,169,173,185,189,193,201,205,209,213,217,221,225,229,233],[540929,17179869187,24641,517,131,34359754753,32801,33,536871938,2097217,262660,4194434,198928,8423720,68720007432,16777219,33554438,137438954626,274877906962,549755814954,2147484682,67108869,134217731,8257,1099511627849,8257,268435462,4294967316,262660,1053188,8589934610,2199023255690,1073746050,4398046609464,196624,1]),
([pw198,pw0,pw1,pw2,pw4,pw10,pw83,pw176,pw191],[16,36,60,64,237,241,185,69,197,5,49,57,61,4,44,1,37,41,65,73,81,85,89,93,101,105,113,141,189,193,217,245,249,253,3],[16386,17181974530,70,19,138,262,35,3,33281,2147483653,4294967825,134217737,131077,1057,2051,4164,262161,65672,524548,1048609,8589936642,4194309,8388620,4164,1073741829,70,16777225,33554437,1073,19,67108876,268435465,138,536870917,262,35]),
([pw0,pw1,pw2,pw4,pw10,pw83,pw176,pw199,pw191],[16,68,5,72,61,65,73,4,37,69,1,21,29,41,81,129,169,3,36,76,45,53,77,89,93,101,105,109,113,117,185,193,197,213,257,261,265,269,273],[1029,17179869189,2053,34359738373,2053,1048581,1029,2097157,65554,4129,776,8258,129,1,68723671168,8388611,16777226,8589934674,137438953475,65554,1073741842,33554441,67108867,274877923361,4129,134217761,268435466,536870921,776,776,2147483651,8258,4294967362,129,180225,950272]),
([pw0,pw1,pw2,pw4,pw10,pw83,pw176,pw191,pw200],[4,80,84,52,13,33,36,21,41,25,81,157,169,3,88,57,29,49,69,73,121,20,1,5,37,45,61,65,85,93,97,113,117,125,181,265,277,281,285,289,293,297],[268437505,4114,4260484,16777253,390,33686660,17179902156,8413324,67108867,68719478785,264225,524291,34359740417,32833,65,137438953490,536870915,4114,1073741842,4114,4114,274877906981,549755814150,1099511694852,2199023288908,136331788,2147483651,4294967333,262185,8225,1048838,1048842,524554,8589943884,156684,1]),
([pw194,pw0,pw1,pw2,pw4,pw10,pw83,pw176,pw191],[36,96,104,100,4,185,53,69,125,197,9,16,57,3,25,29,281,20,92,13,21,33,41,45,77,81,93,97,113,117,121,161,285,289,293,297,301,305,309,313],[10305,262145,35,133121,137,515,10497,68719476737,137438954580,524322,1097796,2097288,4194818,41943364,4165,274877906962,549755814932,1048,2147483666,16778516,4113,65570,67108874,65570,134217762,35,4294967432,8589935106,17179918596,34359742469,268435466,536871048,137,1073742338,515,8453]),
([pw0,pw1,pw2,pw4,pw10,pw83,pw176,pw191,pw201],[16,112,108,52,5,61,65,73,209,36,120,37,69,77,3,21,25,45,97,197,116,1,29,41,53,85,89,105,109,129,185,213,257,261,317,321,325,329,333,337],[2097169,4294967313,32785,8589934609,32785,131089,16777233,131089,17179869478,4194373,14596,8388998,24581,33571596,1073420,67108867,34359738406,2147483810,262147,1073741866,262186,68719476805,134217731,65601,268435529,65609,137438953606,274877907969,7180,7180,549755813891,524426,524426,536871425,513,1]),
([pw202,pw0,pw1,pw2,pw4,pw10,pw83,pw176,pw191],[16,124,36,128,53,109,185,49,69,197,1,21,61,85,129,3,4,5,37,65,73,81,89,93,101,105,113,125,141,189,193,217,245,273,341],[1041,106500,70,37,268,518,134217733,1,131089,4294967299,2065,268435465,2051,17179869329,1041,4162,524321,262408,1049090,2097281,57348,4194307,8388618,4162,2147483651,70,16777225,33554435,8589934753,37,67108874,536870921,268,1073741827,518,16389])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD10 : List StD := [
([pw1,pw11,pw2,pw4,pw10,pw83,pw176,pw191,pw197],[16,48,132,136,177,149,169,173,5,25,37,69,345,36,9,29,41,53,89,93,101,105,109,113,125,153,161,165,185,189,193,197],[3,16418,33554435,4130,67108870,134217731,4130,298,76,521,2058,140,25,139272,266,262149,524294,65732,21,268435524,76,1048579,2097157,33297,4194817,265,8388614,536870915,3074,1034,1073741829,2147483780,140,16777233,25,1]),
([pw0,pw1,pw2,pw4,pw10,pw83,pw176,pw191,pw203],[84,48,140,52,13,29,49,137,169,9,85,81,1,25,37,41,89,93,101,105,113,141,153,161,173,177,189,193,209,217,273,301,349,353,3],[1538,276,4294967457,2097155,133,2241,131,4105,8589934598,4194307,1538,8388614,2051,1538,268435466,65541,131078,276,536870917,276,276,262147,524293,1073741921,41,8233,1048582,67108867,16394,17179869194,134217733,32780,16777228,73,33554505,2147483656]),
([pw204,pw0,pw1,pw2,pw4,pw10,pw83,pw176,pw191],[104,144,148,52,49,53,29,41,48,5,37,69,81,169,185,65,73,89,93,101,105,113,137,141,181,189,193,217,225,229,233,273,309,357],[545,8,24578,32833,3076,65666,4113,257,545,8589934595,4194337,8388613,131,4145,545,4294967554,32833,3076,65666,4113,16777481,131075,262150,24578,134217731,24586,524293,1048579,2147483729,268435529,2097158,33554437,3084,67108867,536871050,1073741849]),
([pw0,pw1,pw205,pw2,pw4,pw10,pw83,pw176,pw191],[84,152,156,36,5,49,61,65,73,21,37,69,81,29,41,85,89,93,101,105,113,141,145,169,189,193,213,217,225,229,233,257,273,341,361,365],[19,19,2147483665,529,2097155,529,8589934641,4194313,10,70,131,35842,262,4099,11,8388676,8321,17179870210,16644,4129,3,65541,131078,67109188,134217733,34359738380,262147,524293,4294967457,268435465,1048582,16777219,2058,33554437,536870924,1073741833]),
([pw0,pw1,pw2,pw4,pw10,pw83,pw199,pw191,pw201],[16,160,5,116,164,61,73,108,37,65,69,168,1,21,29,41,53,129,169,369,76,77,81,89,93,101,105,113,213,257,261],[4101,536870917,8197,1073741829,8197,4101,65541,65541,262178,16897,1296,32834,1,2754688,4718728,8388611,16777234,268435554,262178,42,42,33554449,67108867,16897,521,521,134217746,1296,1296,1296,32834,74,74,1181824,2176,1]),
([pw0,pw1,pw2,pw4,pw10,pw83,pw176,pw191,pw206],[84,108,172,52,257,61,65,73,157,37,77,21,45,81,1,29,41,49,53,89,93,101,105,113,141,169,193,209,213,269,273,301,333,373,3],[1282,16401,2065,16777219,2065,4113,262161,4113,38,67,8589935362,134,1282,1282,134217738,524293,1048582,268435620,536870917,44,33554476,2097155,4194309,1073750081,73,32841,8388614,4294967299,522,17179869706,67108869,140,65676,8203,131081,2147483656]),
([pw207,pw0,pw1,pw2,pw4,pw10,pw83,pw176,pw191],[84,180,52,176,184,152,29,41,61,81,237,377,37,49,57,9,33,169,89,93,101,105,113,153,189,193,217,229,233,245,365,381],[5,9,131330,1089,69648,2178,8705,16389,32801,536870915,1089,65553,131,8705,16397,131330,8388641,36912,2178,8705,16425,262147,524306,2434,67108867,1073742094,1048593,2097155,1089,1101,4194322,16777233,2147487772,33554435,134219790,268435981]),
([pw208,pw0,pw1,pw2,pw4,pw83,pw176,pw191,pw200],[88,188,192,1,52,33,13,157,41,5,21,25,29,57,61,69,81,12,17,45,49,73,97,117,121,181,265,277,281,285,289,293,385,389,393,397,401],[555,32801,4294967329,536870947,8589934625,8388643,32801,131073,651,262222,7178,1294,1638410,33562635,27,16389,134217859,2097157,67108995,17179877505,34359738369,268435526,16452,4194374,69,69,1073742086,2147555330,19,19,16777478,21,21,19,19,68719476737]),
([pw208,pw0,pw1,pw2,pw4,pw83,pw176,pw191],[196,200,208,204,1,33,4,13,181,212,41,405,25,81,281,5,21,29,69,121,17,45,49,57,97,117,285,289,293,297,373,385,389,409,413,417,421],[32827,262186,2147483690,67108907,4294967338,33554475,262442,34897,1048725,200721,66581,6299665,8389395,8589934660,17179871297,34359738436,1073743937,2370,16517,16516,16777349,17030,134218757,268578817,536875779,525317,525318,68719485699]),
([pw0,pw1,pw2,pw4,pw10,pw83,pw176,pw200,pw201],[84,216,5,220,52,108,61,65,73,37,36,1,21,29,41,45,69,169,25,89,93,97,101,105,113,129,181,213,257,261,333,337,421,425],[2053,268435461,4101,536870917,4101,32773,2053,32773,131138,8321,66056,16642,8589934625,1056,67108913,524291,1048586,134218050,2097155,131138,82,4194313,8388611,262273,8321,145,16777226,1073741833,4294967832,66056,2147483651,16642,274,33554481,1025,33]),
([pw202,pw0,pw1,pw2,pw4,pw10,pw83,pw176,pw200],[84,236,36,224,53,232,49,61,65,69,73,88,1,21,81,429,4,228,5,29,37,89,93,101,105,113,125,141,169,181,189,193,213,217,257,273,341,421,433,437],[4113,65541,536903684,274877906949,524,549755846660,67108869,131076,262161,17179869201,8209,134217737,8209,68719476817,4113,162,289,1049128,1058,16417,4,2097155,4194314,4294968450,8589934595,268435586,8388617,16777219,34359738689,524545,33554442,1073741833,137438956040,2147483651,3074,16449]),
([pw209,pw0,pw1,pw2,pw4,pw10,pw83,pw176,pw191],[84,244,52,248,240,5,73,61,65,117,37,129,232,1,29,41,49,77,169,21,89,93,101,105,113,141,145,213,217,245,341,365,433,441,445,449],[8225,17,262274,16641,1544,32834,5,2053,8225,536870915,524321,33554441,67,1073807393,67108901,262274,16641,1544,32834,135169,137237,1048579,2097162,134217922,268435459,2147483798,4194313,8388611,8590000385,4294967573,16777226,521,1560,17179869187,34359738454,2069]),
([pw0,pw210,pw1,pw2,pw4,pw10,pw83,pw176,pw191],[104,48,252,36,13,9,25,29,81,169,33,41,49,209,37,77,89,93,101,105,113,153,161,173,181,189,193,217,225,229,233,309,381],[8,8226,532,193,1027,2053,4353,11,8226,532,193,17410,8390660,4353,11,2147483654,2097155,32802,4194310,259,16777226,65541,131078,532,134217733,28,262147,524293,193,268435465,1048582,33554435,4294967306,67108869,536870924,1073741833]),
([pw0,pw1,pw2,pw4,pw10,pw83,pw176,pw211,pw191],[104,108,256,9,257,461,41,77,97,385,36,21,25,45,69,197,1,29,37,53,101,105,109,113,141,153,169,185,209,213,265,333,337,453,457,465],[268435466,65553,2065,16777219,2065,8209,8209,524305,8589934602,33554435,138,17179869194,131,138,1073741834,131105,262658,34896609348,261,67109124,134217988,1048579,2097157,4129,4129,4194337,8388614,2147483651,16898,16898,4294967301,32836,32836,1025,1027,3]),
([pw194,pw0,pw1,pw2,pw4,pw10,pw83,pw176,pw201],[104,264,36,272,53,109,185,61,197,108,260,5,21,37,65,69,73,77,129,268,25,45,89,93,97,101,105,113,245,261,333,337],[21,1028,70,37,263172,262,262149,524292,2065,268435459,4113,536870929,4099,2097169,2065,194,16417,40968,65794,131585,131585,4194307,8388618,194,16777219,194,33554441,67108867,1048609,16417,134217738,1073741833,40968,2147483651,65794,4]),
([pw212,pw0,pw1,pw2,pw4,pw10,pw83,pw176,pw191],[104,108,276,52,45,97,1,25,37,41,69,81,29,169,197,89,93,101,105,113,141,145,153,161,181,193,245,309,333,365,433,469],[81,10,8228,4225,1282,16900,2051,3,2147483651,67108869,81,1048579,517,81,2097177,134217734,4194307,1282,8388614,2051,16777227,32773,65542,8228,37,536870956,131075,262149,4225,1073741961,524294,268435459,1290,33554437,16908,2051]),
([pw0,pw1,pw213,pw2,pw4,pw10,pw83,pw176,pw191],[84,232,280,36,5,61,65,73,157,21,37,49,69,81,117,1,29,41,53,85,89,93,101,105,113,129,141,169,193,213,217,257,273,341,365,433,449],[524546,32785,2147483665,529,67108867,529,8589936657,262161,10,38,67,5378,134,8195,266,134217764,65601,17410,131204,8195,3,1048581,2097158,536871076,1073741829,17179869196,4194307,8388613,4294969409,34359738377,16777222,16387,4106,268435461,68719476748,33554441])]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
noncomputable def ptopD9 : List StD := [
([pw214,pw0,pw1,pw2,pw4,pw83,pw176,pw191],[196,48,473,204,29,284,49,397,292,97,52,288,81,137,385,485,296,37,109,133,153,169,181,185,389,437,461,469,477,481,489],[37,162,147464,25,16793608,73,40,134217731,524293,8197,8197,4165,7,268435586,1048579,536871042,4099,162,67108881,2099968,769,8391424,32785,32785,262161,1073741889,37815296,1089]),
([pw215,pw0,pw1,pw2,pw4,pw83,pw176,pw191],[196,108,5,65,204,397,300,308,97,304,1,21,385,485,489,52,312,37,45,53,81,109,165,169,181,185,257,389,437,461,477,481],[1029,98,135184,25,134221840,81,80,1029,67108869,2053,2053,262149,524293,1073741858,11,2147483682,4194307,35,536870921,8389504,385,33555328,8201,8201,2097161,1064961,285310976,16387])]
def ptopD8 : List StD := []
theorem ptopI8 : LevelN true ptopT 8 ptopD8 := by intro s h; cases h
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

end PEqualNP.Outside.L_meta_14762

theorem PEqualNP.Outside.L_meta_14762 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 0, 6, 1, 6, 2, 6, 3, 6, 1, 7, 2, 7, 4, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact PEqualNP.Outside.L_meta_14762.replaceShort gates o fit correct
